PAPER=main

all:
	mkdir -p __build/
	cp *.tex *.cls __build/
	cd __build/ && pdflatex ${PAPER}.tex
	ln -sf __build/${PAPER}.pdf
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1

clean:
	rm -rf __build/ ${PAPER}.pdf
