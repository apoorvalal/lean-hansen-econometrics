decls_json := "site/_generated/declarations.json"

# Default: render the site.
default: site-render

# Run lake exe export_decls and write declarations.json.
site-export:
    @mkdir -p site/_generated
    lake exe export_decls > {{decls_json}}

# Regenerate site/auto/** stubs from declarations.json.
site-stubs: site-export
    uv run scripts/build_stubs.py

# Live-reload preview at http://localhost:port.
site-preview: site-stubs
    cd site && quarto preview

# One-shot render to site/_site/.
site-render: site-stubs
    cd site && quarto render

# Alias for site-render.
site: site-render
