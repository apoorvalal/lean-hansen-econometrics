decls_json := "site/_generated/declarations.json"

# Default: refresh generated reference pages and render the complete site.
default: site-render

# Local equivalent of the PR Lean CI gate.
ci:
    lake build
    lake env lean tests/MetricsLibSmoke.lean
    lake build @mathlib/lint-style
    lake env .lake/packages/mathlib/.lake/build/bin/lint-style HansenEconometrics

# Export authored public declarations and their statement dependencies.
site-export:
    @mkdir -p site/_generated
    lake exe export_decls > {{decls_json}}.tmp
    mv {{decls_json}}.tmp {{decls_json}}

# Rebuild foldable result pages and the dependency graph.
site-generate: site-export
    uv run --no-project scripts/build_site.py

# Refresh generated pages, then start a live-reload preview.
site-preview: site-generate
    cd site && quarto preview

# Render the complete, self-contained site to docs/.
site-render: site-generate
    cd site && quarto render

# Alias for site-render.
site: site-render

# Render from the existing declaration export without loading Lean again.
site-render-fast:
    uv run --no-project scripts/build_site.py
    cd site && quarto render

# Refresh the packaged copy of the external Lean crash course.
site-crash-course:
    curl -L --fail --silent --show-error https://lalten.org/pages/lean_crash_course/ -o site/assets/lean-crash-course.html.tmp
    mv site/assets/lean-crash-course.html.tmp site/assets/lean-crash-course.html

# Run documentation generator tests.
site-test:
    uv run --no-project --with markdown python -m unittest tests.test_build_site

# Render and stage docs/ for a single "deploy" commit.
# After running, `git commit && git push` publishes via GitHub Pages.
deploy: site-render
    git add docs
    git status --short docs
