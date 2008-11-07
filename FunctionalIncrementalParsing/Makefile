%.view: %.html
	firefox $<


%.html: %.markdown
	pandoc --smart --standalone  --table-of-contents --css=home.css --from=markdown --to=html --output=$@ $<

%.tex: %.markdown
	pandoc --smart --standalone  --table-of-contents --from=markdown --to=latex --output=$@ $<

%.pdf: %.tex
	pdflatex $<



