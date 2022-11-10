SRC := src
SCT := $(SRC)/sections

PDFLATEX = pdflatex

SOURCES := $(patsubst %.lagda,%.tex,$(wildcard $(SCT)/*.lagda $(SCT)/*.tex))

all: document.pdf 

document.pdf: $(SRC)/document.tex $(SOURCES)
	cd $(SRC) &&\
	$(PDFLATEX) document.tex &&\
	bibtex document &&\
	$(PDFLATEX) document.tex &&\
	$(PDFLATEX) document.tex &&\
	cp document.pdf ../document.pdf

build/document.tex: $(SRC)/document.tex
	cp $(SRC)/document.tex build/document.tex

%.tex: %.lagda
	agda --latex --latex-dir=$(SRC) $<

.PHONY: all
