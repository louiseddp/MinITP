all:
	ocamllex lexer.mll
	ocamlopt -c kernel.ml
	ocamlopt -c kernel.cmx printer.ml
	ocamlopt -c kernel.cmx build_proof.ml
	menhir -v --infer parser.mly
	ocamlopt -c parser.mli parser.ml
	ocamlopt -c parser.mli parser.cmx parser.ml lexer.ml 
	ocamlopt -c parser.mli parser.ml lexer.cmx lexer.ml minlog.ml
	ocamlopt -c kernel.cmx printer.ml build_proof.ml minlog.ml
	ocamlopt -o minlog lexer.cmx parser.cmx kernel.cmx printer.cmx build_proof.cmx minlog.ml

clean:
	rm *.o *.cmx *.cmi minlog *.automaton *.conflicts
