#
# Copyright (C) 2014 NICTA
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions, and the following disclaimer,
#    without modification.
#
# 2. Redistributions in binary form must reproduce at minimum a disclaimer
#    substantially similar to the "NO WARRANTY" disclaimer below
#    ("Disclaimer") and any redistribution must be conditioned upon
#    including a substantially similar Disclaimer requirement for further
#    binary redistribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
# IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
# TO, THE IMPLIED WARRANTIES OF MERCHANTIBILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# HOLDERS OR CONTRIBUTORS BE LIABLE FOR SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
# THE POSSIBILITY OF SUCH DAMAGES.
#

MLYACC_PFX := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

ifndef MLYACC_INCLUDED
MLYACC_INCLUDED=true

all: $(MLYACC_PFX)/mlyacc

include $(MLYACC_PFX)/../../globalmakevars
include $(MLYACC_PFX)/../mllex/Makefile

$(MLYACC_PFX)/src/yacc.lex.sml: $(MLYACC_PFX)/src/yacc.lex $(MLLEX)
	$(RUN_MLLEX) $<

ifeq ($(SML_COMPILER),mlton)
#
# Compilation if the compiler is mlton
#
MLTON_DEPS := $(shell mlton -stop f $(MLYACC_PFX)/mlyacc.mlb)

$(MLYACC_PFX)/mlyacc: $(MLTON_DEPS)
	mlton $<

else ifeq ($(SML_COMPILER),poly)
#
# Compilation if the compiler is Poly/ML
#

#
# set POLY_CC_FLAGS to -m32 if you are using 32bit poly on a 64bit architecture


$(MLYACC_PFX)/mlyacc: $(MLYACC_PFX)/mlyacc0
	/bin/echo "#! /bin/sh" > $@
	/bin/echo >> $@
	/bin/echo "$(TOOLRUN_PFX)$< \"\$$@\"" >> $@
	chmod +x $@

$(MLYACC_PFX)/mlyacc0: $(MLYACC_PFX)/mlyacc.o
	$(POLYCC) -o $@ $<

MLY_SRCDEPS0 = absyn-sig absyn core coreutils grammar graph hdr lalr link look \
           mklrtable mkprstruct parse poly-main shrink sigs utils verbose \
	   yacc
MLY_SRCDEPS1 = $(patsubst %,%.ML,$(MLY_SRCDEPS0)) yacc-grm-sig.sml yacc-grm.sml yacc.lex.sml
MLY_SRCDEPS = $(patsubst %,src/%,$(MLY_SRCDEPS1))

MLY_LIBDEPS0 = base-sig join lrtable parser2 stream
MLY_LIBDEPS = $(patsubst %,mlyacclib/MLY_%.ML,$(LIBDEPS0))

MLY_DEPS = $(patsubst %,$(MLYACC_PFX)/%,$(MLY_LIBDEPS) $(MLY_SRCDEPS))

$(MLYACC_PFX)/mlyacc.o: $(MLYACC_PFX)/poly-mlyacc.ML $(MLY_DEPS)
	MLYACC_PFX=$(MLYACC_PFX) $(SETDYLIB) $(POLY) < $<

else
$(error Can only cope with SML_COMPILER as "poly" or "mlton")

endif

#
# clean targets
#
.PHONY: mlyacc_clean

clean: mlyacc_clean

cparser_clean: mlyacc_clean

mlyacc_clean:
	-/bin/rm -f $(MLYACC_PFX)/mlyacc.o $(MLYACC_PFX)/mlyacc $(MLYACC_PFX)/src/yacc.lex.sml

endif
