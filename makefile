################################################################
#
# Z3 / StandardML binding
#
################################################################

SML = smlsharp

VPATH = src
INCDIR = $(patsubst %,-I%,$(subst :, ,$(VPATH)))

SMLFLAGS = $(INCDIR)

SAMPLE_SRC = sample/sample.sml
SAMPLE = $(SAMPLE_SRC:.sml=)

SRCS = src/z3.sml \
	   src/z3_fixedpoint.sml \
	   src/z3_ast_vector.sml \
	   src/z3_ast_map.sml \
	   src/z3_goal.sml \
	   src/z3_solver.sml \
	   src/z3_statistics.sml \
	   src/z3_enum.sml \
	   src/z3_parser.sml \
	   src/z3_accessor.sml \
	   src/z3_tactic_and_probe.sml \
	   src/z3_external_theory_plugin.sml \
	   src/z3_quantifier.sml \
	   src/z3_set.sml \
	   src/z3_array.sml \
	   src/z3_bitvector.sml  \
	   src/z3_arithmetic.sml \
	   src/z3_model.sml \
	   src/z3_propositional.sml \
	   src/z3_config.sml \
	   src/z3_context.sml \
	   src/z3_parameter.sml \
	   src/z3_sort.sml \
	   src/z3_parameter_desc.sml \
	   src/z3_global.sml \
	   src/z3_algebraic.sml \
	   src/z3_interpolation.sml \
	   src/z3_realclosedfield.sml \
	   src/z3_deprecated.sml \
	   src/z3_log.sml \
	   src/z3_numerals.sml \
	   src/z3_stringconv.sml \
	   src/z3_error.sml \
	   src/libh.sml

OBJS = $(SRCS:.sml=.o) $(SAMPLE_SRC:.sml=.o)

all: $(TARGET) sample

.PHONY: sample
sample: $(SAMPLE)
	./sample/sample

$(SAMPLE): sample/sample.smi $(OBJS)
	@$(SML) $(SMLFLAGS) -o $@ $<

%.o: %.sml
	@echo "  SML# [$@]"
	@$(SML) $(SMLFLAGS) -c $<

%.d: %.sml
	@echo "  GEN [$@]"
	@$(SHELL) -ec '$(SML) -MM $(SMLFLAGS) $< \
		| sed "s|\($*\)\.o[ :]*|\1.o $@ : |g" > $@; \
		[ -s $@ ] || rm -rf $@'

ifeq (,$(findstring $(MAKECMDGOALS),clean))
-include $(SRCS:.sml=.d)
-include $(SAMPLE_SRC:.sml=.d)
endif

.PHONY: clean
clean:
	-rm -rf $(SRCS:.sml=.d)
	-rm -rf $(OBJS)
	-rm $(SAMPLE_SRC:.sml=.d)
	-rm $(SAMPLE)

