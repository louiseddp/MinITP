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
	ocamlopt -o proplog lexer.cmx parser.cmx kernel.cmx printer.cmx elaborator.cmx proplog.cmx either.cmx

clean:
	rm -f *.o *.cmx *.cmi proplog *.automaton *.conflicts parser.ml lexer.ml parser.mli
