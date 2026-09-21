MAIN := main

.PHONY: all watch clean cleanall

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex preamble.tex sections/*.tex refs.bib cas-sc.cls cas-common.sty cas-model2-names.bst
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

watch:
	latexmk -pdf -pvc $(MAIN).tex

clean:
	latexmk -c $(MAIN).tex

cleanall:
	latexmk -C $(MAIN).tex
	rm -f $(MAIN).pdf
