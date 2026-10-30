# Manuscript and figures

**Paper:** arXiv link to be added.

`main.tex` builds the article and supplementary information as one document.
This directory is the source for manuscript releases and the arXiv submission
archive. Make manuscript and figure changes here before preparing a release.
The companion repository is
[`yaugenst/maxwell-universality`](https://github.com/yaugenst/maxwell-universality).

From this directory, with a standard TeX Live installation:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

The result is `build/main.pdf`. The build needs the packages imported in
`main.tex`, including `lmodern`, `microtype`, `mathrsfs`, `enumitem`, `xurl`,
`cleveref`, `caption`, and `needspace`, plus the usual AMS and graphics packages.

## Prepare the arXiv ZIP

Commit the manuscript changes, then run from the repository root:

```bash
uv run --script scripts/package_arxiv.py
```

The script builds `paper/` from `HEAD`, packages the TeX inputs and figures
actually used, adds `references.bib` and the generated `main.bbl`, and rebuilds
the extracted ZIP in a fresh directory. It requires Git, Python 3.11 or newer,
`latexmk`, BibTeX and a complete TeX Live installation; no numerical solver or
large companion archives are needed.

On Linux, the same script can use a pinned TeX Live 2025 container, without a
local TeX installation:

```bash
uv run --script scripts/package_arxiv.py --texlive-image \
  texlive/texlive@sha256:7056390eac37715fd3e01875037ceb4016cb17d44c611f7bbbfa7a012007979f
```

This requires Docker and downloads about 2.6 GB on first use. Each TeX build
uses one CPU and a 2 GiB memory limit, with networking disabled. The image is
recorded in the package receipt. It checks TeX Live 2025 compatibility; the
arXiv service may use a different package snapshot within that release.

Outputs are written to `build/arxiv/`:

- `maxwell-universality-arxiv.zip`: the source archive, with `main.tex` at its root.
- `maxwell-universality.pdf`: the PDF rebuilt from that archive.
- `package-receipt.json`: source commit, file hashes and build result.
- `source-build.log` and `archive-build.log`: local build logs.

Use `--ref <commit>` to package a particular revision and `--output-dir
build/arxiv-v2` for another run. The output directory must be new. Uncommitted
changes are excluded. The ZIP contains the article and SI sources, their used
figures and bibliography. Lean sources and experiment data are distributed
separately through the companion repository.

Select `main.tex` and `pdflatex` when uploading. The packaging choices follow
the [arXiv TeX submission guide](https://info.arxiv.org/help/submit_tex.html).
The receipt identifies the local compiler; arXiv's generated PDF still needs
checking during submission against its
[supported TeX Live environment](https://info.arxiv.org/help/faq/texlive.html).

## Regenerate figures

The figures use a shared style in `figures/figstyle.py`. The new numerical
figures and SI table can be regenerated entirely from the small bundled inputs:

```bash
uv run --script figures/fig_numerical.py
```

This writes `figures/fig_numerical.{pdf,png}`,
`figures/si/numerical_controls.{pdf,png}`, and the numerical table. It does not
run a Maxwell solve. `figures/data/numerical_illustrations.json` records the
source-file hashes and reconstruction checks for the compact plotting data.

After installing `demo-fields`, optionally refresh that data from the archived
full-vector fields:

```bash
uv run --script figures/fig_numerical.py --refresh-data \
  --experiment-root ../experiments
```

The remaining figures have adjacent Python generators; the rendered PDFs are
included for a direct LaTeX build. A successful PDF build checks typesetting
and references; the proof audits and exact arithmetic checks are separate
entry points.

The [formal proof map](../lean/proof-map.md) connects manuscript statements
to Lean declarations. Its verification records identify the checked source
and dependency revisions; the manuscript build and the proof checks are
separate reproducibility steps.

The logical-translation figure reads the exact certificate files:

```bash
uv run --script figures/si/logical_translation.py \
  --certificate-root ../certificates/yee
```
