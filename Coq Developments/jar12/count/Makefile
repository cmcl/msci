OCAML_DIR=/usr/local/bin
OCAMLC=$(OCAML_DIR)/ocamlc
OCAMLLEX=$(OCAML_DIR)/ocamllex

count : lexer.cmo count.cmo
	$(OCAMLC) -o count lexer.cmo count.cmo

lexer.cmo : lexer.ml
	$(OCAMLC) -c lexer.ml

count.cmo : count.ml
	$(OCAMLC) -c count.ml

lexer.ml : lexer.mll
	$(OCAMLLEX) lexer.mll

clean:
	rm -f lexer.ml lexer.cmi lexer.cmo
	rm -f count.cmi count.cmo
	rm -f count
