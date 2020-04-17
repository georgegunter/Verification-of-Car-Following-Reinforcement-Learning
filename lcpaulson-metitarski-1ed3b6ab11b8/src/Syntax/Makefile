#############################################################################
# MAKEFILE FOR THE METITARSKI SYNTAX
###############################################################################

# Requires an installation of SML/NJ

all: build

mt.grm.sig: mt.grm
	ml-yacc mt.grm

mt.grm.sml: mt.grm
	ml-yacc mt.grm

mt.lex.sml: mt.lex
	ml-lex mt.lex

build: mt.lex.sml mt.grm.sig mt.grm.sml load.sml

clean:
	rm mt.???.{sml,sig} mt.grm.desc

