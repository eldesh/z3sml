
SML = smlsharp
SMLFLAGS =

TARGET = sample

SRCS = \
	  sample.sml \
	  z3.sml            \
	  z3_fixedpoint.sml \
	  z3_ast_vector.sml \
	  z3_ast_map.sml    \
	  z3_goal.sml       \
	  z3_solver.sml     \
	  z3_statistics.sml \
	  z3_enum.sml       \
	  z3_parser.sml     \
	  z3_accessor.sml   \
	  z3_tactic_and_probe.sml       \
	  z3_external_theory_plugin.sml \
	  z3_quantifier.sml \
	  z3_set.sml \
	  z3_model.sml

OBJS = $(SRCS:.sml=.o)

all: $(TARGET)

$(TARGET): sample.smi $(OBJS)
	$(SML) $(SMLFLAGS) -o $@ $<

%.o: %.sml
	$(SML) $(SMLFLAGS) -c $<

%.d: %.sml
	@echo "generate [$@] from [$*]"
	@$(SHELL) -ec '$(SML) -MM $(SMLFLAGS) $< \
		| sed "s/\($*\)\.o[ :]*/\1.o $@ : /g" > $@; \
		[ -s $@ ] || rm -rf $@'

-include $(SRCS:.sml=.d)

.PHONY: clean
clean:
	rm -rf $(SRCS:.sml=.d)
	rm -rf $(OBJS)
	rm $(TARGET)


