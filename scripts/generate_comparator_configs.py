#!/usr/bin/env python3
"""
Generate comparator JSON configs from entry TOML config.

Usage:
    python3 generate_comparator_configs.py <entry_toml> <output_dir> [--enable-nanoda]

For each [[theorems]] group in the entry config, generates a comparator
JSON config file in the output directory.

--enable-nanoda turns on comparator's second-kernel replay: the exported proof
is re-checked by the independent nanoda kernel as well as Lean's own. Comparator
finds the binary on PATH or via COMPARATOR_NANODA, so the caller is responsible
for making it available before passing this flag.
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


def generate_configs(config_path, output_dir, enable_nanoda=False):
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

        # Name the config after the FULL impl module. Naming it after the last
        # component alone made `A.B.Foo` and `C.D.Foo` collide, so one group's
        # config silently overwrote the other's and that group went unchecked.
        filename = sanitize_name(impl_module) if impl_module else f"theorem_{i}"
        config_file = os.path.join(output_dir, f"{filename}.json")

        comparator_config = {
            "challenge_module": spec_module,
            "solution_module": impl_module,
            "theorem_names": names,
            "permitted_axioms": permitted_axioms,
            "enable_nanoda": bool(enable_nanoda)
        }

        with open(config_file, 'w') as f:
            json.dump(comparator_config, f, indent=2)
            f.write('\n')

        generated.append(config_file)
        print(f"Generated: {config_file}")

    kernels = "Lean + nanoda" if enable_nanoda else "Lean"
    print(f"\nGenerated {len(generated)} comparator config(s) for entry '{entry_id}' (kernels: {kernels})")
    return generated


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    flags = [a for a in sys.argv[1:] if a.startswith("--")]

    unknown = [f for f in flags if f != "--enable-nanoda"]
    if unknown:
        print(f"ERROR: unknown flag(s): {' '.join(unknown)}", file=sys.stderr)
        sys.exit(1)

    if len(args) < 2:
        print(f"Usage: {sys.argv[0]} <entry_toml> <output_dir> [--enable-nanoda]", file=sys.stderr)
        sys.exit(1)

    config_path, output_dir = args[0], args[1]

    if not os.path.exists(config_path):
        print(f"ERROR: Config file not found: {config_path}", file=sys.stderr)
        sys.exit(1)

    generate_configs(config_path, output_dir, enable_nanoda="--enable-nanoda" in flags)


if __name__ == '__main__':
    main()
