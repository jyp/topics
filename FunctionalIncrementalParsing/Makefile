%.view: %.html
	firefox $<

%.pdf: %.svg
#	inkscape --export-pdf=$@ $<
	convert $< $@

Paper.pdf: begin.pdf mid.pdf progress.tex pgf-tree.tex
Paper.tex: SExpr.lhs Stack.lhs Applicative.lhs Input.lhs Choice.lhs Sublinear.lhs Code.lhs

checks:
	ghc -c SExpr.lhs
	ghc -c Stack.lhs
	ghc -c Applicative.lhs
	ghc -c Parser.lhs
	ghc -c Progress.lhs
	ghc -c Input.lhs
	ghc -c Choice.lhs
	ghc -c Sublinear.lhs
	ghc -c Polish2.lhs
	ghc -c Example.lhs
	ghc -c Code.lhs

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
	dot -Txdot $< | dot2tex --texmode=raw --figonly > $@
#	dot2tex --preproc $< | dot2tex --figonly > $@

%.pdf: %.tex
	pdflatex $<
	bibtex $*
	pdflatex $<
	pdflatex $<



