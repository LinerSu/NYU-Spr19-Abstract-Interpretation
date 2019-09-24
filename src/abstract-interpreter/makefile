# file "makefile  © P. Cousot 2018"

OCAMLFIND = ocamlfind
APRONDIR = `$(OCAMLFIND) query apron`
OCAMLINC = -I $(APRONDIR) gmp.cma apron.cma octD.cma
CLIBS = -cclib -loctMPQ -cclib -lapron -cclib -lmpfr

.PHONY: all
all: analyseTop analyseBotTop analyseParity analyseConst analyseInt

.PHONY: help
help:
	@echo "make analyseParity: parity analysis (for variables x,y only)"
	@echo "make analyseConst: consistency analysis (for variables x,y only)"
	@echo "make analyseCong: congruence analysis (for variables x,y only)"
	@echo "make analyseInt: interval analysis (for variables x,y only)"
	@echo "make analyseOct: octagon analysis (for variables x,y only)"

.PHONY: delete
delete:
	@/bin/rm -f main *~ .*~ *.cmo *.cmi lexer.ml parser.ml parser.mli parser.conflicts *.out
	@find . -lname '*.*' -delete

.PHONY: analyseParity analyseConst analyseCong analyseInt analyseOct

analyseParity : delete
	@echo "*** parity domain"
	@/bin/rm -f abstractDomain.ml
	ln -s -f abstractDomainParity.ml abstractDomain.ml
	@make --always-make main
	@make --always-make examples

analyseConst : delete
	@echo "*** constancy domain"
	@/bin/rm -f abstractDomain.ml
	ln -s -f abstractDomainConstancy.ml abstractDomain.ml
	@make --always-make main
	@make --always-make examples

analyseCong : delete
	@echo "*** congruence domain"
	@/bin/rm -f abstractDomain.ml
	ln -s -f abstractDomainCongruence.ml abstractDomain.ml
	@make --always-make main
	@make --always-make examples

analyseInt: delete
	@echo "*** interval domain"
	@/bin/rm -f abstractDomain.ml
	ln -s -f abstractDomainInterval.ml abstractDomain.ml
	@make --always-make main
	@make --always-make examples

analyseOct: delete
	@echo "*** octagon domain"
	@/bin/rm -f abstractDomain.ml
	ln -s -f abstractDomainOctagon.ml abstractDomain.ml
	@make --always-make main
	@make --always-make examples

build:
	@echo "Build"
	ln -s -f ../abstractSyntaxExpressions.ml .
	ln -s -f ../lexer.mll .

main: build
	@ocamllex -q lexer.mll
	@ocamlc -c abstractSyntaxExpressions.ml
	@ocamlc -c abstractDomain.mli
	ocamlfind ocamlc -linkpkg -package apron,apron.apron,apron.octD abstractDomain.ml
	@ocamlc -c abstractTree.mli
	@ocamlc -c abstractTree.ml
	@ocamlc -c abstractSyntax.ml
	@ocamlc -c printer.ml
	@menhir --infer --explain parser.mly
	@ocamlc -c parser.mli
	@ocamlc -c lexer.ml
	@ocamlc -c parser.ml
	@ocamlc -c abstractInterpreter.ml
	@ocamlc -c main.ml
	ocamlfind ocamlc -linkpkg -package apron,apron.apron,apron.octD -o main abstractSyntaxExpressions.cmo abstractDomain.cmo abstractTree.cmo abstractSyntax.cmo printer.cmo parser.cmo lexer.cmo abstractInterpreter.cmo main.cmo

.PHONY: examples
.IGNORE: examples
examples: main
	@echo "# using the abstract interpreter:"
	@echo ";"| ./main
	@echo "x = 42;"| ./main
	@echo "break;"| ./main
	@echo "break; x = 7;"| ./main
	@echo "x = 7; ; break; "| ./main
	@echo "{}" | ./main
	@echo "x=-10-20--40;" | ./main
	@echo "x=1; y=2;" | ./main
	@echo "{x=10; ; y=20;}" | ./main
	@echo "if (1-2<3-4-5) x=-x;" | ./main
	@echo "if (x<1) if (x<0) x=1; else if (x<0) { x=2; x=3; } else { x=4; x=5; x=6; }" | ./main
	@echo "while (x<1) {}" | ./main
	@echo "while (x<1) x = x + 1;" | ./main
	@echo "while (x<10) x = x + 1;" | ./main
	@echo "while (0<1){x = x - 1;} x = 42;" | ./main
	@echo "while (0<1){}" | ./main
	@echo "x=x-1;while (0<1){x=x-1;if(x<2)break;};" | ./main
	@echo "x=-10; while (x<0) if (x<0) if (0<x) x=-x;" | ./main
	@echo "x=-10; while (x<0) { x=x-1; break; }; x= 10;" | ./main
	@echo "x=0; while (x<0) { while (x<0) x=x-1; x= 10; }; x= 100;" | ./main
	@echo "x=0; while (x<0) { while (x<0) x=x-1; break; }; x= 100;" | ./main
	@echo "x=x-1; while (0<1) { x=x-1; if (2 < x) break; };" | ./main
	@echo "x=10; while (x>0) x=x-1;" | ./main
	@echo "while (0<1){ break; x=1; }" | ./main
	@echo "while (x!=2) { if (x==0) break; if (x==1) break; }" | ./main
	@echo "while (0<1) x=x+2;" |./main
	@echo "# end"
