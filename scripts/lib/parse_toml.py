#!/usr/bin/env python3
"""
TOML config parser for VibeRegistry.

Reads entry TOML configs and extracts fields needed by the verification scripts.
Usage:
    python3 parse_toml.py <config_file> <field>

Fields:
    project.id, project.url, project.commit, project.branch
    lean.toolchain, lean.mathlib_tag
    build.strategy
    theorems              - JSON array of theorem groups
    tools.safe_verify_repo, tools.safe_verify_ref
"""

import sys
import json

try:
    import tomllib
except ImportError:
    try:
        import tomli as tomllib
    except ImportError:
        # Fallback: minimal TOML parser for the subset we use
        import re

        def _parse_toml_minimal(text):
            """Minimal TOML parser supporting tables, key-value pairs, and arrays of tables."""
            result = {}
            current_section = result
            current_path = []
            array_tables = {}  # track [[table]] arrays

            for line in text.split('\n'):
                line = line.strip()
                if not line or line.startswith('#'):
                    continue

                # Array of tables: [[section]]
                m = re.match(r'^\[\[([^\]]+)\]\]$', line)
                if m:
                    path = m.group(1).split('.')
                    # Navigate to parent
                    parent = result
                    for key in path[:-1]:
                        parent = parent.setdefault(key, {})
                    table_key = path[-1]
                    if table_key not in parent:
                        parent[table_key] = []
                    new_table = {}
                    parent[table_key].append(new_table)
                    current_section = new_table
                    current_path = path
                    continue

                # Table: [section]
                m = re.match(r'^\[([^\]]+)\]$', line)
                if m:
                    path = m.group(1).split('.')
                    current_section = result
                    for key in path:
                        current_section = current_section.setdefault(key, {})
                    current_path = path
                    continue

                # Key = value
                m = re.match(r'^(\w+)\s*=\s*(.+)$', line)
                if m:
                    key = m.group(1)
                    value = m.group(2).strip()
                    current_section[key] = _parse_value(value)

            return result

        def _parse_value(value):
            """Parse a TOML value."""
            # String
            if value.startswith('"') and value.endswith('"'):
                return value[1:-1]
            # Array
            if value.startswith('['):
                # Simple array of strings
                items = re.findall(r'"([^"]*)"', value)
                if items:
                    return items
                # Try numeric
                items = re.findall(r'[\w.]+', value[1:-1])
                return items
            # Integer
            try:
                return int(value)
            except ValueError:
                pass
            # Boolean
            if value == 'true':
                return True
            if value == 'false':
                return False
            return value

        class tomllib:
            @staticmethod
            def loads(text):
                return _parse_toml_minimal(text)


def load_config(config_path):
    with open(config_path, 'r') as f:
        return tomllib.loads(f.read())


def get_field(config, field):
    """Get a dotted field from the config dict."""
    parts = field.split('.')
    value = config
    for part in parts:
        if isinstance(value, dict):
            value = value.get(part)
        else:
            return None
        if value is None:
            return None
    return value


def main():
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <config_file> <field>", file=sys.stderr)
        sys.exit(1)

    config_path = sys.argv[1]
    field = sys.argv[2]

    config = load_config(config_path)

    if field == 'theorems':
        # Return full theorem groups as JSON
        theorems = config.get('theorems', [])
        print(json.dumps(theorems))
    else:
        value = get_field(config, field)
        if value is None:
            print(f"Field '{field}' not found in {config_path}", file=sys.stderr)
            sys.exit(1)
        if isinstance(value, (list, dict)):
            print(json.dumps(value))
        else:
            print(value)


if __name__ == '__main__':
    main()
