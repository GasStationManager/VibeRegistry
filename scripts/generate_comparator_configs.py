#!/usr/bin/env python3
"""
Generate comparator JSON configs from entry TOML config.

Usage:
    python3 generate_comparator_configs.py <entry_toml> <output_dir>

For each [[theorems]] group in the entry config, generates a comparator
JSON config file in the output directory.
"""

import sys
import os
import json

# Add lib/ to path for parse_toml
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'lib'))
from parse_toml import load_config


def sanitize_name(name):
    """Convert a module name to a safe filename."""
    return name.replace('.', '_').lower()


def generate_configs(config_path, output_dir):
    config = load_config(config_path)
    entry_id = config.get('project', {}).get('id', 'unknown')
    theorems = config.get('theorems', [])

    os.makedirs(output_dir, exist_ok=True)

    generated = []
    for i, thm_group in enumerate(theorems):
        spec_module = thm_group.get('spec_module', '')
        impl_module = thm_group.get('impl_module', '')
        names = thm_group.get('names', [])
        permitted_axioms = thm_group.get('permitted_axioms',
                                         ['propext', 'Quot.sound', 'Classical.choice'])

        # Generate filename from the last part of the impl module name
        parts = impl_module.split('.')
        filename = sanitize_name(parts[-1]) if parts else f"theorem_{i}"
        config_file = os.path.join(output_dir, f"{filename}.json")

        comparator_config = {
            "challenge_module": spec_module,
            "solution_module": impl_module,
            "theorem_names": names,
            "permitted_axioms": permitted_axioms,
            "enable_nanoda": False
        }

        with open(config_file, 'w') as f:
            json.dump(comparator_config, f, indent=2)
            f.write('\n')

        generated.append(config_file)
        print(f"Generated: {config_file}")

    print(f"\nGenerated {len(generated)} comparator config(s) for entry '{entry_id}'")
    return generated


def main():
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <entry_toml> <output_dir>", file=sys.stderr)
        sys.exit(1)

    config_path = sys.argv[1]
    output_dir = sys.argv[2]

    if not os.path.exists(config_path):
        print(f"ERROR: Config file not found: {config_path}", file=sys.stderr)
        sys.exit(1)

    generate_configs(config_path, output_dir)


if __name__ == '__main__':
    main()
