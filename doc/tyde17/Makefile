PAPER=main

main: all

prepare:
	lhs2TeX --poly Parser.lhs -o parser.tex

all:prepare
	mkdir -p __build/
	cp *.tex *.sty *.cls __build/
	cd __build/ && latexmk -pdf ${PAPER}.tex
	ln -sf __build/${PAPER}.pdf
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1

clean:
	rm -rf __build/ ${PAPER}.pdf
