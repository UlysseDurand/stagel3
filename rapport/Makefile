pdf:
	python3 ~/git/compil_perso/data/compile.py -l maths -o doc.tex doc.mdx
	uldrlatex doc.tex

all:
	python3 ~/git/compil_perso/data/compile.py -l maths -o doc.tex doc.mdx
	uldrlatex doc.tex
	cp bib.bib latextrash/bib.bib
	biber latextrash/doc.bcf
	uldrlatex doc.tex

clean:
	rm latextrash/*
