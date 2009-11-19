# Set this to the basename of the .tex file
# This will also be the name of the generated .dvi, .ps and .pdf files
PAPER = iterate

all: $(PAPER).dvi 

# Set this to the other source files that should be counted as 
# dependencies
BIB := braun.bib 
OTHERSOURCES := $(BIB) Makefile

.PHONY: ps
ps: $(PAPER).ps

.PHONY: pdf
pdf: $(PAPER).pdf


# run once, then re-run until it's happy
# input redirected from /dev/null is like hitting ^C at first error
$(PAPER).dvi: $(PAPER).tex $(OTHERSOURCES) $(FIGURES:%=%.eps)
	if latex $(PAPER).tex </dev/null; then \
		true; \
	else \
		stat=$$?; touch $(PAPER).dvi; exit $$stat; \
	fi
	bibtex $(PAPER)
	while grep "undefined references" $(PAPER).log; do \
		if latex $(PAPER).tex </dev/null; then \
			true; \
		else \
			stat=$$?; touch $(PAPER).dvi; exit $$stat; \
		fi; \
	done

$(PAPER).pdf: $(PAPER).dvi $(FIGURES:%=%.pdf) 
#Remove the .aux file because pdflatex wants it different
	rm -f $(PAPER).aux 
	if pdflatex $(PAPER).tex </dev/null; then \
		true; \
	else \
		stat=$$?; touch $(PAPER).pdf; exit $$stat; \
	fi
	bibtex $(PAPER)
	while grep "Rerun to get cross" $(PAPER).log; do \
		if pdflatex $(PAPER).tex </dev/null; then \
			true; \
		else \
			stat=$$?; touch $(PAPER).pdf; exit $$stat; \
		fi; \
	done

$(PAPER).ps: $(PAPER).dvi
	dvips -P cmz -t letter -o $(PAPER).ps $(PAPER).dvi


clean:
	rm -f *.aux *.log $(PAPER).ps *.dvi *.blg *.bbl *.toc *~ *.out $(PAPER).pdf


# Generate PDF figures from the EPS ones
%.pdf: %.eps
	epstopdf $<
