# Walkthrough site

Local-only Quarto site. Not deployed.

## Prerequisites

- [Quarto](https://quarto.org/docs/get-started/) installed
- Lean toolchain (already required for the main project)
- `uv` (already required globally)

## Build targets

From the repo root:

- `make site-export` — regenerate `site/_generated/declarations.json` from Lean
- `make site-stubs` — regenerate `site/auto/**` from the JSON
- `make site-preview` — export + stubs + `quarto preview` (live reload)
- `make site-render` — export + stubs + `quarto render` to `site/_site/`
- `make site` — alias for `site-render`

## Caveats

- `site/auto/` is wiped and regenerated on every stub build, so files there are never authored by hand.
- `quarto preview` may flicker briefly when stubs are regenerated.
