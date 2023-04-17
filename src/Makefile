all:
	ocamllex lexer.mll
	ocamlopt -c kernel.ml
	ocamlopt -c kernel.cmx printer.ml
	ocamlopt -c kernel.cmx elaborator.ml
	menhir -v --infer parser.mly
	ocamlopt -c parser.mli parser.ml
	ocamlopt -c parser.mli parser.cmx parser.ml lexer.ml 
	ocamlopt -c parser.mli parser.ml lexer.cmx lexer.ml proplog.ml
	ocamlopt -c kernel.cmx printer.ml elaborator.ml proplog.ml
	ocamlopt -o proplog lexer.cmx parser.cmx kernel.cmx printer.cmx elaborator.cmx proplog.ml

clean:
	rm *.o *.cmx *.cmi minlog *.automaton *.conflicts
