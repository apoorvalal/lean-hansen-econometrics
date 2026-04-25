.PHONY: site site-export site-stubs site-preview site-render

DECLS_JSON := site/_generated/declarations.json

$(DECLS_JSON): | site/_generated
	lake exe export_decls > $@

site/_generated:
	mkdir -p $@

site-export: $(DECLS_JSON)

site-stubs: site-export
	uv run scripts/build_stubs.py

site-preview: site-stubs
	cd site && quarto preview

site-render: site-stubs
	cd site && quarto render

site: site-render
