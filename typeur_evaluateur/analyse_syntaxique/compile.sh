ocamllex lexeur.mll
ocamlyacc parseur.mly
ocamlc -c parseur.mli lexeur.ml parseur.ml main.ml
ocamlc -o parseur lexeur.cmo parseur.cmo main.cmo