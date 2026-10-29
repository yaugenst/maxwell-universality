#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""List, install, or verify the companion artifact's checksummed files."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def destination(name: str) -> Path:
    path = ROOT / name
    if Path(name).is_absolute() or '..' in Path(name).parts or not path.resolve().is_relative_to(ROOT):
        raise ValueError(f'Path leaves the repository: {name}')
    return path


def verify(files: dict) -> None:
    errors = []
    for name, info in files.items():
        path = destination(name)
        if not path.is_file():
            errors.append(f'missing: {name}')
        elif path.stat().st_size != info['bytes'] or sha256(path) != info['sha256']:
            errors.append(f'changed: {name}')
    if errors:
        raise RuntimeError('\n'.join(errors[:15]) + (f'\n... {len(errors)} errors total' if len(errors) > 15 else ''))
    print(f'Verified {len(files):,} imported files against the snapshot manifest.')


def install(archives: dict, files: dict, asset_dir: Path) -> None:
    for name, info in archives.items():
        archive = asset_dir / name
        if not archive.is_file():
            raise FileNotFoundError(f'Missing {archive}. Obtain the companion archives described in docs/reproduction.md.')
        if archive.stat().st_size != info['bytes'] or sha256(archive) != info['sha256']:
            raise RuntimeError(f'Archive checksum mismatch: {name}')
        expected = {p: v for p, v in files.items() if v.get('archive') == name}
        with tarfile.open(archive, 'r:gz') as bundle:
            members = bundle.getmembers()
            names = [m.name for m in members]
            if len(set(names)) != len(names) or set(names) != set(expected):
                raise RuntimeError(f'Archive members differ from the manifest: {name}')
            for member in members:
                record = expected[member.name]
                if not member.isfile() or member.size != record['bytes']:
                    raise RuntimeError(f'Unexpected archive entry: {member.name}')
                path = destination(member.name)
                if path.exists():
                    if not path.is_file() or sha256(path) != record['sha256']:
                        raise RuntimeError(f'Refusing to overwrite a changed file: {path}')
                    continue
                path.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.install-', delete=False) as handle:
                    temporary = Path(handle.name)
                try:
                    with bundle.extractfile(member) as source, temporary.open('wb') as out:
                        shutil.copyfileobj(source, out)
                    if sha256(temporary) != record['sha256']:
                        raise RuntimeError(f'Member checksum mismatch: {member.name}')
                    temporary.rename(path)
                finally:
                    temporary.unlink(missing_ok=True)
        print(f'Installed {name} ({len(expected):,} files).', flush=True)


def main() -> None:
    manifest = json.loads((ROOT / 'data/manifest.json').read_text())
    archives = manifest['archives']
    groups = sorted({v['group'] for v in archives.values()})
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('list', 'install', 'verify'))
    parser.add_argument('--groups', nargs='+', choices=['core', *groups],
                        help='Default: core for verify, all archives for install/list')
    parser.add_argument('--all', action='store_true', help='Include core and every archive group')
    parser.add_argument('--asset-dir', type=Path, default=ROOT / '.release-assets')
    args = parser.parse_args()
    if args.all and args.groups:
        parser.error('Choose --all or --groups.')
    chosen = set(['core', *groups] if args.all else args.groups or (['core'] if args.action == 'verify' else groups))
    selected = {k: v for k, v in archives.items() if v['group'] in chosen}
    files = {k: v for k, v in manifest['files'].items()
             if (v.get('archive') in selected or ('archive' not in v and 'core' in chosen))}
    if args.action == 'list':
        for group in groups:
            if group in chosen:
                part = [v for v in selected.values() if v['group'] == group]
                print(f'{group:20} {sum(v["bytes"] for v in part) / 2**20:8.1f} MiB  {len(part):2} archives  {sum(v["files"] for v in part):6,} files')
    elif args.action == 'install':
        if not selected:
            parser.error('Select at least one archive group to install.')
        install(selected, files, args.asset_dir)
    else:
        verify(files)


if __name__ == '__main__':
    main()
