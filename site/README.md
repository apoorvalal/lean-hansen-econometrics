# Hansen Econometrics site

This directory contains the Quarto source for the GitHub Pages site. A render
writes the complete site to `docs/` at the repository root.

## Site contents

- `index.qmd` describes the current repository scope.
- `crash-course.qmd` links to and embeds the packaged Lean crash course.
- `dependencies.qmd` is generated from Lean statement dependencies.
- `results/` contains generated foldable textbook-to-Lean result pages.
- `walkthroughs/` contains hand-written proof deep dives for selected results.
  Each deep dive links to its canonical generated result card.
- `assets/` contains the site style, browser code, the D3 dependency, and the
  self-contained crash-course snapshot.

The generated pages have two sources of truth:

1. `lake exe export_decls` reads the compiled Lean environment and exports
   authored public declarations, source locations, docstrings, and direct
   statement dependencies.
2. `scripts/build_site.py` reads the canonical chapter inventories and selects
   the theorem-facing declarations linked by their crosswalks.

The generator shows at most six endpoints for one result group. The inventory
keeps the complete support surface and all qualifications.

For Chapters 7--13, every result group must have a reader-facing TeX statement.
An inventory can keep these statements in its main crosswalk or in a compact
`Reader-facing TeX statements` table. A theorem-prefix row supplies the common
textbook statement to its implementation-specific support cards. The site build
fails if a later result has no statement or no TeX expression.

## Prerequisites

- the repository's pinned Lean toolchain;
- Quarto;
- `uv`;
- `just` for the short commands below. Direct equivalents are also shown.

## Build and preview

From the repository root, run:

```sh
just site-render
```

This command refreshes the Lean declaration export, rebuilds the generated
Quarto sources, and renders all pages to `docs/`.

If `just` is not installed, run:

```sh
mkdir -p site/_generated
lake exe export_decls > site/_generated/declarations.json.tmp
mv site/_generated/declarations.json.tmp site/_generated/declarations.json
uv run --no-project scripts/build_site.py
quarto render site
```

Use `just site-render-fast` to reuse the existing declaration export. Use
`just site-preview` to refresh generated pages and start Quarto's live preview.

## Refresh the crash course

The packaged course is a self-contained HTML snapshot. Refresh it with:

```sh
just site-crash-course
```

After a refresh, inspect the course's adaptation summary, update the retrieval
date and checksum in `assets/README.md`, and render the site.

The wrapper loads the packaged file after its own page has loaded and marks the
placeholder iframe as external to Quarto's resource embedder. Keep this design.
Inlining the course as a `data:` URL disables browser storage inside the course.

## Tests

Run the generator tests with:

```sh
just site-test
```

Then render and inspect at least these pages:

- the home page;
- the crash-course wrapper and its full-page link;
- the dependency graph overview and one chapter graph;
- one early and one late important-result page;
- one hand-written proof deep dive and its canonical result-card link.

## Publishing

The rendered `docs/` directory is committed to git. GitHub Pages serves it from
the repository's configured `main`/`docs` source.

```sh
just deploy
git commit -m "Render site"
git push
```

Do not edit files in `docs/` by hand. Edit `site/`, refresh the generated
sources, and render again.
