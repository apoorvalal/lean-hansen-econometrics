# Walkthrough site

Local-only Quarto site. Not deployed.

## Prerequisites

- [Quarto](https://quarto.org/docs/get-started/) installed
- [`just`](https://github.com/casey/just) installed
- Lean toolchain (already required for the main project)
- `uv` (already required globally)

## Build targets

From the repo root:

- `just site-export` — regenerate `site/_generated/declarations.json` from Lean
- `just site-stubs` — regenerate `site/auto/**` from the JSON
- `just site-preview` — export + stubs + `quarto preview` (live reload)
- `just site-render` — export + stubs + `quarto render` to `site/_site/`
- `just site` (or just `just`) — alias for `site-render`

## Caveats

- `site/auto/` is wiped and regenerated on every stub build, so files there are never authored by hand.
- `quarto preview` may flicker briefly when stubs are regenerated.
