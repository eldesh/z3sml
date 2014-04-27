
all: sample

z3.o: z3.sml z3.smi
	smlsharp -c $<

sample.o: sample.sml sample.smi
	smlsharp -c $<

sample: sample.o z3.o
	smlsharp -o sample sample.smi

.PHONY: clean
clean:
	rm z3.o
	rm sample.o
	rm sample

