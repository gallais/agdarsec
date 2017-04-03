SLIDES=agdarsec

all:
	mkdir -p __build
	cp *.tex __build/
	cd __build/ && pdflatex -shell-escape ${SLIDES}.tex
	ln -sf __build/${SLIDES}.pdf
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1
