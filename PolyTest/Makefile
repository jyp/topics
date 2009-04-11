default: Memo.pdf

%.tex: %.markdown
	echo %include lhs2TeX.fmt > header
	pandoc -s --from markdown+lhs --to latex $< > $@ --include-in-header=header
#	pandoc -s --from markdown --to latex $< > $@

%.pdf: %.tex
	pdflatex $<

#%.tex: %.lhs
#	lhs2TeX --poly < $< > $@
