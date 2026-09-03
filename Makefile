.PHONY: repl
repl:
	rlwrap idris2 --repl idris2-ffi-safe.ipkg

.PHONY: pdf
pdf:
	typst c --root . ./doc/main.typ

.PHONY: pdf-watch
pdf-watch:
	typst watch --root . ./doc/main.typ
