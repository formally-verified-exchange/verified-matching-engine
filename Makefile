.PHONY: paper paper-clean paper-lncs paper-lncs-clean

# Deterministic paper build (audit item P1-15): two pdflatex passes so
# cross-references (section/table numbers) stabilize. The bibliography is
# a plain `thebibliography` environment, not an external .bib database, so
# no bibtex/biber pass is needed. A third pass produces byte-identical
# text output to the second, confirming two passes reach a fixed point.
paper: paper.tex
	pdflatex -interaction=nonstopmode paper.tex
	pdflatex -interaction=nonstopmode paper.tex

paper-clean:
	rm -f paper.aux paper.log paper.out paper.toc

# Submission-format paper built independently of the original manuscript.
paper-lncs:
	cd paper-lncs && pdflatex -interaction=nonstopmode -halt-on-error paper-lncs.tex
	cd paper-lncs && pdflatex -interaction=nonstopmode -halt-on-error paper-lncs.tex

paper-lncs-clean:
	rm -f paper-lncs/paper-lncs.aux paper-lncs/paper-lncs.log \
		paper-lncs/paper-lncs.out paper-lncs/paper-lncs.toc
