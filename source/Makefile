EXEC=hauff
LIBS=unix.cmxa

all:
	ocamlopt bitio.mli
	ocamlopt bitio.ml
	ocamlopt struct.mli
	ocamlopt $(LIBS) bitio.cmx struct.ml
	ocamlopt decompression.mli
	ocamlopt $(LIBS) bitio.cmx struct.cmx decompression.ml
	ocamlopt compression.mli
	ocamlopt $(LIBS) bitio.cmx struct.cmx compression.ml
	ocamlopt -o $(EXEC) $(LIBS) struct.cmx bitio.cmx decompression.cmx compression.cmx main.ml

clean:
	rm -rf $(EXEC) *.cmi *.cmo *.cmx *~ *.o a.out
