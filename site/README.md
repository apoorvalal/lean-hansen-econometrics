# Walkthrough site

Quarto site rendered to `docs/` at the repo root and served via GitHub Pages.

## Prerequisites

- [Quarto](https://quarto.org/docs/get-started/) installed
- [`just`](https://github.com/casey/just) installed
- Lean toolchain (already required for the main project)
- `uv` (already required globally)

## Build targets

From the repo root:

- `just site-render` — render walkthroughs to `docs/` (default; ~5 seconds)
- `just site-preview` — `quarto preview` with live reload while editing
- `just deploy` — render and stage `docs/` for a deploy commit
- `just site-export` — regenerate `site/_generated/declarations.json` from Lean (only for full-coverage builds)
- `just site-stubs` — regenerate `site/auto/**` from the JSON (only for full-coverage builds)
- `just site-full` — full-coverage build (requires re-enabling auto-stubs in `_quarto.yml`)

## Publishing

The rendered site lives at `docs/` and is committed to git. GitHub Pages
serves it from `main` / `/docs`.

After a render, commit and push:

```sh
just deploy            # renders and stages docs/
git commit -m "Render site"
git push
```

GitHub Pages will pick up the change within a minute.

## Caveats

- The auto-stub layer (~515 stubs auto-generated from the Lean library) is
  currently paused for fast iteration. To re-enable: in `_quarto.yml`,
  remove the `project.render` list and uncomment the
  "Auto-generated reference" sidebar block.
- `site/auto/` is wiped and regenerated on every `site-stubs` run, so files
  there are never authored by hand.
- `quarto preview` may flicker briefly when stubs are regenerated.
