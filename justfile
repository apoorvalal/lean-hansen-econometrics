decls_json := "site/_generated/declarations.json"

# Default: render the site (walkthroughs only — auto-stub layer is paused).
default: site-render

# Run lake exe export_decls and write declarations.json.
# Only needed for the full-coverage build (`site-full`).
site-export:
    @mkdir -p site/_generated
    lake exe export_decls > {{decls_json}}

# Regenerate site/auto/** stubs from declarations.json.
# Only needed for the full-coverage build (`site-full`).
site-stubs: site-export
    uv run scripts/build_stubs.py

# Live-reload preview at http://localhost:port (walkthroughs only).
site-preview:
    cd site && quarto preview

# One-shot render to docs/ (walkthroughs only — fast).
# Auto-stub rendering is currently paused via `project.render` in _quarto.yml.
site-render:
    cd site && quarto render

# Alias for site-render.
site: site-render

# Full-coverage build: regenerate stubs and render everything.
# Requires editing _quarto.yml first to re-enable the auto/** render scope
# and the "Auto-generated reference" sidebar.
site-full: site-stubs
    cd site && quarto render

# Render and stage docs/ for a single "deploy" commit.
# After running, `git commit && git push` publishes via GitHub Pages.
deploy: site-render
    git add docs
    git status --short docs
