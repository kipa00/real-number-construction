all: real.vo

real.vo: real.v rational_prop.vo
	coqc real.v

rational_prop.vo: rational_prop.v rational.vo
	coqc rational_prop.v

rational.vo: rational.v integer.vo
	coqc rational.v

integer.vo: integer.v refl.vo
	coqc integer.v

refl.vo: refl.v predicate.vo
	coqc refl.v

predicate.vo: predicate.v
	coqc predicate.v

clean:
	rm -f *.vo *.glob
