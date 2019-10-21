FROM coqorg/coq:8.9.1

RUN opam install coq-equations.1.2+8.9

RUN opam install coq-mathcomp-ssreflect.1.9.0
