AGDA_EXEC?=agda
.PHONY: test Everything.agda clean

OTHEROPTS = --auto-inline -Werror

RTSARGS = +RTS -M6G -A128M -RTS ${OTHEROPTS}

test: Everything.agda
	${AGDA_EXEC} ${RTSARGS} -i. Everything.agda

html: Everything.agda
	${AGDA_EXEC} ${RTSARGS} --html -i. Everything.agda

Everything.agda:
	git ls-tree --full-tree -r --name-only HEAD | grep '^src/[^\.]*.agda' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' | LC_COLLATE='C' sort > Everything.agda

clean:
	find . -name '*.agdai' -exec rm \{\} \;
