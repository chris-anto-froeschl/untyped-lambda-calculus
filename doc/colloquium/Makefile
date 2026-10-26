MAIN := slides

.PHONY: all watch clean cleanall

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex colloquium.bib ../papers/tcs/refs.bib ../papers/tcs/leanlink.tex ../papers/tcs/leanrev.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

watch:
	latexmk -pdf -pvc $(MAIN).tex

clean:
	latexmk -c $(MAIN).tex

cleanall:
	latexmk -C $(MAIN).tex
	rm -f $(MAIN).pdf
