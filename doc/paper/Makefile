PAPER=easychairstyle

main: all

prepare:
	lhs2TeX --poly Parser.lhs -o parser.tex
	find src/ -name "*.lagda" | sed "s|src/||" | xargs -n1 ./lagda2tex

all:prepare paper

paper:
	mkdir -p __build/
	cp -R *.tex *.cls *.bib *.bst *.sed latex/* __build/
	cd __build/ && sed -i -f rewrite.sed `find . -name "*.tex"` && latexmk -pdf ${PAPER}.tex
	ln -sf __build/${PAPER}.pdf
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1

clean:
	rm -rf __build/ ${PAPER}.pdf parser.tex

fullclean: clean
	rm -rf latex/
