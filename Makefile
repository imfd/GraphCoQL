


AT=

% : CoqMakefile

all: all_coq

all_coq : CoqMakefile
	make -f CoqMakefile all


CoqMakefile: _CoqProject Makefile
	${AT}coq_makefile -f _CoqProject -o CoqMakefile



.PHONY : clean

clean:
	make -f CoqMakefile clean
