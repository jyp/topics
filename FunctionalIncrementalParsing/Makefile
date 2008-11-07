%.view: %.html
	firefox $<

%.html: %.markdown
	pandoc --smart --standalone  --table-of-contents --css=home.css --from=markdown --to=html --output=$@ $<
