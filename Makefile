PAPER = carmichael

.PHONY: all clean

all: $(PAPER).pdf

# two passes so cross-references and hyperlinks resolve
$(PAPER).pdf: $(PAPER).tex
	pdflatex -interaction=nonstopmode $(PAPER).tex
	pdflatex -interaction=nonstopmode $(PAPER).tex

clean:
	rm -f $(PAPER).aux $(PAPER).log $(PAPER).out $(PAPER).toc
