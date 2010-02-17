.PHONY: all

all: IterateCombined.vo

BraunStreams.vo: BraunStreams.v Makefile
	coqc BraunStreams.v

BraunFunctions.vo: BraunStreams.vo BraunFunctions.v Makefile
	coqc BraunFunctions.v

IterateCombined.vo: IterateCorrect.vo IterateProductive.vo IterateCombined.v Makefile
	coqc IterateCombined.v

IterateCorrect.vo: IterateCorrect.v BraunStreams.vo Makefile
	coqc IterateCorrect.v

IterateProductive.vo: IterateProductive.v BraunFunctions.vo Makefile
	coqc IterateProductive.v
