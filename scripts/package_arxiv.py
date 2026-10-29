#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Build an arXiv source ZIP and verify it from a committed paper revision."""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE_SUFFIXES = {'.tex', '.pdf', '.png', '.jpg', '.jpeg', '.sty', '.cls', '.bst'}
BAD_LOG = re.compile(
    r'Overfull \\[hv]box|(?:Reference|Citation).*undefined|'
    r'There were undefined|multiply defined|Rerun to get|Label\(s\) may have changed'
)


def git(*args: str) -> str:
    return subprocess.check_output(['git', '-C', str(ROOT), *args], text=True).strip()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def tex_command(command: list[str], directory: Path, image: str | None) -> list[str]:
    if image is None:
        return command
    return ['docker', 'run', '--rm', '--network', 'none', '--cpus', '1', '--memory', '2g',
            '--user', f'{os.getuid()}:{os.getgid()}',
            '--volume', f'{directory}:{directory}:Z',
            '--workdir', str(directory), image, *command]


def build(directory: Path, log: Path, *, bibliography: bool, image: str | None) -> str:
    command = ['latexmk', '-norc', '-pdf', '-interaction=nonstopmode',
               '-halt-on-error', '-file-line-error', '-recorder',
               '-outdir=build', '-bibtex' if bibliography else '-bibtex-', 'main.tex']
    with log.open('w') as output:
        result = subprocess.run(tex_command(command, directory, image), cwd=directory,
                                stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'LaTeX build failed; see {log}')
    text = (directory / 'build/main.log').read_text(errors='replace')
    failures = [line for line in text.splitlines() if BAD_LOG.search(line)]
    if failures:
        raise RuntimeError(f'Unresolved typesetting issues; see {log}:\n' + '\n'.join(failures))
    return text


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ref', default='HEAD', help='Committed revision to package (default: HEAD)')
    parser.add_argument('--texlive-image', help='Optional Docker image for the TeX tools (Linux)')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'build/arxiv',
                        help='New output directory (default: build/arxiv)')
    args = parser.parse_args()
    revision = git('rev-parse', '--verify', '--end-of-options', f'{args.ref}^{{commit}}')
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=False)
    print(f'Packaging committed manuscript {revision[:12]}', flush=True)
    if git('status', '--porcelain', '--', 'paper'):
        print('Uncommitted paper changes are excluded; commit them before packaging.', flush=True)

    with tempfile.TemporaryDirectory(prefix='maxwell-arxiv-') as temporary:
        temporary = Path(temporary)
        archive = subprocess.check_output(['git', '-C', str(ROOT), 'archive', revision, 'paper'])
        with tarfile.open(fileobj=io.BytesIO(archive)) as source:
            # git archive supplies repository-relative regular files. This project
            # ships no symlinked manuscript dependencies.
            for member in source.getmembers():
                if member.isdir():
                    continue
                if not member.isfile() or '..' in Path(member.name).parts or Path(member.name).is_absolute():
                    raise RuntimeError(f'Unsupported manuscript archive member: {member.name}')
                path = temporary/member.name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(source.extractfile(member).read())
        paper = temporary/'paper'
        print('Building the manuscript and bibliography.', flush=True)
        build(paper, output/'source-build.log', bibliography=True, image=args.texlive_image)

        # The recorder identifies the inputs actually read, avoiding a second
        # hand-maintained list of figures and included TeX files.
        files = {}
        for line in (paper/'build/main.fls').read_text().splitlines():
            if not line.startswith('INPUT '):
                continue
            path = (paper/line[6:]).resolve()
            if not path.is_relative_to(paper):
                continue  # Installed TeX Live packages and fonts.
            name = path.relative_to(paper)
            if name.parts[0] != 'build' and path.suffix.lower() in SOURCE_SUFFIXES:
                files[name.as_posix()] = path.read_bytes()
        files['main.bbl'] = (paper/'build/main.bbl').read_bytes()
        # Keep editable bibliography sources as well as the prebuilt bibliography.
        for path in paper.rglob('*.bib'):
            files[path.relative_to(paper).as_posix()] = path.read_bytes()

        zip_path = output/'maxwell-universality-arxiv.zip'
        with zipfile.ZipFile(zip_path, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as bundle:
            for name, content in sorted(files.items()):
                entry = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
                entry.compress_type = zipfile.ZIP_DEFLATED
                entry.external_attr = 0o100644 << 16
                bundle.writestr(entry, content)

        # Build from the exact ZIP, with no original source tree or old auxiliaries.
        extracted = temporary/'extracted'
        with zipfile.ZipFile(zip_path) as bundle:
            bundle.extractall(extracted)
        print('Rebuilding the extracted ZIP with its bundled bibliography.', flush=True)
        final_log = build(extracted, output/'archive-build.log', bibliography=False, image=args.texlive_image)
        shutil.copy2(extracted/'build/main.pdf', output/'maxwell-universality.pdf')
        pages = int(re.search(r'Output written on .*?\((\d+) pages?', final_log).group(1))
        receipt = {
            'source_commit': revision,
            'source_tree': git('rev-parse', f'{revision}:paper'),
            'compiler': subprocess.check_output(
                tex_command(['pdflatex', '--version'], extracted, args.texlive_image),
                text=True).splitlines()[0],
            'texlive_image': args.texlive_image,
            'entrypoint': 'main.tex',
            'archive': zip_path.name,
            'archive_sha256': digest(zip_path.read_bytes()),
            'archive_bytes': zip_path.stat().st_size,
            'files': {name: {'sha256': digest(content), 'bytes': len(content)}
                      for name, content in sorted(files.items())},
            'extracted_archive_build': 'passed',
            'pdf_pages': pages,
            'scope': 'Source packaging and local typesetting validation; not an arXiv server submission or proof audit.',
        }
        (output/'package-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(f'{zip_path}: {len(files)} files, {zip_path.stat().st_size:,} bytes; {pages}-page rebuild passed.')


if __name__ == '__main__':
    main()
