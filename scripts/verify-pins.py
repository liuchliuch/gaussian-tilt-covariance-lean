#!/usr/bin/env python3
"""Fail-closed read-only validation of every locked Git dependency.

Run after `lake exe cache get`. No package is fetched, updated, or modified.
"""
from __future__ import annotations
import argparse, json, pathlib, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib-root', type=pathlib.Path)
    parser.add_argument('--packages-root', type=pathlib.Path, action='append', default=[])
    args = parser.parse_args()
    mathlib = (args.mathlib_root or ROOT / '.lake/packages/mathlib').resolve()
    roots = args.packages_root or [ROOT / '.lake/packages', mathlib / '.lake/packages']
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    results = []
    for package in manifest['packages']:
        if package['type'] != 'git':
            raise RuntimeError('Unexpected non-Git dependency: ' + package['name'])
        candidates = [mathlib] if package['name'] == 'mathlib' else [r / package['name'] for r in roots]
        existing = list(dict.fromkeys(p.resolve() for p in candidates if p.is_dir()))
        if not existing:
            raise RuntimeError('Missing locked dependency: ' + package['name'])
        for directory in existing:
            revision = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
            changed = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
            record = {'name': package['name'], 'path': str(directory), 'expected_revision': package['rev'],
                      'actual_revision': revision, 'tracked_changes': changed,
                      'passed': revision == package['rev'] and not changed}
            results.append(record)
    passed = all(r['passed'] for r in results)
    print(json.dumps({'passed': passed, 'locked_packages': len(manifest['packages']), 'checkouts': results}, indent=2))
    return 0 if passed else 1

if __name__ == '__main__':
    sys.exit(main())
