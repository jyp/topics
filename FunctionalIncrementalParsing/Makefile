%.view: %.html
	firefox $<

%.pdf: %.svg
	convert $< $@

Paper.pdf: begin.pdf mid.pdf progress.tex tree.tex

%.html: %.markdown
	pandoc --smart --standalone  --css=home.css --from=markdown --to=html --output=$@ $<

%.direct.tex: %.markdown
	pandoc --smart --standalone --from=markdown --to=latex --output=$@ $<

%.lhs: %.markdown
	pandoc --smart --standalone --from=markdown --to=latex+lhs --output=$@ $<

%.tex: %.lhs
	lhs2TeX $< > $@


%.fig: %.dia
	dia -e $@ $< 

%.tex: %.dia
	dia -e $@ $< 

%.ps: %.dot
	dot -Tps $< -o $@

%.tex: %.dot
	dot -Txdot $< | dot2tex --figonly > $@
#	dot2tex --preproc $< | dot2tex --figonly > $@

%.pdf: %.tex
	pdflatex $<
	bibtex $*
	pdflatex $<
	pdflatex $<



