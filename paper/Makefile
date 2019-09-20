# Super Makefile for latex.
#
# 1. place your figures in ./figs/
# 2. place your .bib files in ./bib/

GOALS=main.pdf


LATEX= pdflatex
TEX= $(LATEX) # for the built-in implicit rule .dvi
BIBTEX= bibtex
DVIPS= dvips -P cmz -t letter
PS2PDF= ps2pdf14 -dPDFSETTINGS=/prepress -dEmbedAllFonts=true -dSubsetFonts=true -dEPSCrop=true -dAutoRotatePages=/None
FIXDVIPSTITLE= ./other/fixdvipstitle

FIGS= $(wildcard ./figs/*.eps ./plots/*.eps)
BIBS= $(wildcard ./bib/*.bib)
TEXS= $(wildcard ./*.tex ./src/*.tex) 
RM = rm -f

RERUN = "(undefined|There were undefined references|Rerun to get(cross-references|the bars) right)"
RERUNBIB = "No file.*\.bbl|Citation.*undefined"

# %.eps: %.fig
# 	fig2dev -L ps $(@:.eps=.fig) > $(@:.eps=.ps)
# 	ps2epsi $(@:.eps=.ps) $@

%.bbl: $(BIBS)
	$(BIBTEX) $*

%.pdf: %.tex $(FIGS) $(BIBS) Makefile $(TEXS)
	$(LATEX) $<
	$(BIBTEX) $*
	make $*.bbl && $(LATEX) $<;true
	$(LATEX) $<
	$(LATEX) $<

all:
	rm -f $(GOALS)
	make $(GOALS)

clean:
	$(RM) *.aux *.log *.bbl *.blg *.brf *.cb *.ind *.idx *.ilg *.inx *.ps *.dvi *.toc *.lof *.lot *.out *.ps.tmp
	find -name *.aux -exec rm {} \;
