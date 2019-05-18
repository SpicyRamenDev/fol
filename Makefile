all:
	ocamlc -c base.mli
	ocamlc -c fol_manip.mli
	ocamlc -c fol_manip.ml
	ocamlc -c parse.mli
	ocamlc -c parse.ml
	ocamlc -c disp.mli
	ocamlc -c disp.ml
	ocamlc -c resolution.mli
	ocamlc -c resolution.ml
