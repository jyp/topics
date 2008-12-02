%.view: %.html
	firefox $<

%.pdf: %.svg
	convert $< $@

Paper.pdf: begin.pdf mid.pdf

%.html: %.markdown
	pandoc --smart --standalone  --css=home.css --from=markdown --to=html --output=$@ $<



%.direct.tex: %.markdown
	pandoc --smart --standalone --from=markdown --to=latex --output=$@ $<

%.lhs: %.markdown
	pandoc --smart --standalone --from=markdown --to=latex --output=$@ $<

%.tex: %.lhs
	lhs2TeX $< > $@


%.pdf: %.tex
	pdflatex $<



