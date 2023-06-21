all:
	ocamllex lexer.mll
	ocamlopt -c either.ml
	ocamlopt -c kernel.ml
	ocamlopt -c printer.ml
	ocamlopt -c elaborator.ml
	menhir -v --infer parser.mly
	ocamlopt -c parser.mli
	ocamlopt -c parser.ml
	ocamlopt -c lexer.ml
	ocamlopt -c proplog.ml
	ocamlopt -o proplog either.cmx kernel.cmx printer.cmx elaborator.cmx parser.cmx lexer.cmx proplog.cmx

clean:
	rm -f *.o *.cmx *.cmi proplog *.automaton *.conflicts parser.ml lexer.ml parser.mli
