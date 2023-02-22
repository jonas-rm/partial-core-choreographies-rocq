DIAGRAMS := $(wildcard *.drawio)
DIAGRAMS_PDFS := $(patsubst %.drawio, %.drawio.pdf, $(DIAGRAMS))
DRAWIO = drawio
LATEXMK = latexmk

.PHONY: all
all: main.pdf

.PHONY: pdf_tex
pdf_tex: $(DIAGRAMS_PDFTEXS)

.PHONY: pdf
pdf: $(DIAGRAMS_PDFS)

main.pdf: main.tex pdf
	$(LATEXMK) -pdf $<

%.drawio.pdf: %.drawio
	$(DRAWIO) -x -f pdf --crop -o $@ $^

.PHONY: clean
clean:
	$(LATEXMK) -c &>/dev/null
	$(RM) $(DIAGRAMS_SVGS) $(DIAGRAMS_PDFS) $(DIAGRAMS_PDFTEXS)
