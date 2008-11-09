%.view: %.html
	firefox $<


%.html: %.markdown
	pandoc --smart --standalone  --css=home.css --from=markdown --to=html --output=$@ $<



# %.tex: %.markdown
#	pandoc --smart --standalone --from=markdown --to=latex --output=$@ $<

%.lhs: %.markdown
	pandoc --smart --standalone --from=markdown --to=latex --output=$@ $<

%.tex: %.lhs
	lhs2tex $< > $@


%.pdf: %.tex
	pdflatex $<



