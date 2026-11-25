PAPERS := $(wildcard proofs/*/manuscript/*.tex)
PDFS := $(PAPERS:.tex=.pdf)

.PHONY: papers verify
papers: $(PDFS)

%.pdf: %.tex
	cd "$(dir $<)" && latexmk -g -pdf -interaction=nonstopmode -halt-on-error "$(notdir $<)"

verify:
	./verify.sh
