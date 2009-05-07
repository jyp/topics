default: PolyTest.pdf

%.view: %.html
	firefox $<

%.pdf: %.svg
	inkscape --export-pdf=$@ $<
#	convert $< $@


PolyTest.tex: PolyTest.lhs

test:
	ghc --make Full
	./Full

checks:
	ghc -c Full.lhs

%.tex: %.lhs
	lhs2TeX $< > $@


%.fig: %.dia
	dia -e $@ $< 

%.tex: %.dia
	dia -e $@ $< 

%.ps: %.dot
	dot -Tps $< -o $@

%.tex: %.dot
	dot -Txdot $< | dot2tex --texmode=raw --figonly > $@
#	dot2tex --preproc $< | dot2tex --figonly > $@

%.pdf: %.tex
	pdflatex $<
	bibtex $*
	pdflatex $<
	pdflatex $<



