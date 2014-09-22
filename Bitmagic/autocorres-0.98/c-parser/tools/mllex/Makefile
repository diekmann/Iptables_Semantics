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

MLLEX_PFX := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

ifndef MLLEX_INCLUDED
MLLEX_INCLUDED=true
MLLEX=$(MLLEX_PFX)/mllex

all: $(MLLEX)

include $(MLLEX_PFX)/../../globalmakevars

RUN_MLLEX=$(TOOLRUN_PFX)$(MLLEX)



ifeq ($(SML_COMPILER),mlton)
#
# Compilation if the compiler is mlton
#
MLTON_DEPS := $(shell mlton -stop f $(MLLEX_PFX)/mllex.mlb)

$(MLLEX): $(MLTON_DEPS)
	mlton $<
else ifeq ($(SML_COMPILER),poly)
#
# Compilation if the compiler is Poly/ML
#

#
# set POLY_CC_FLAGS to -m32 if you are using 32bit poly on a 64bit architecture

$(MLLEX): $(MLLEX)0
	/bin/echo "#! /bin/sh" > $@
	/bin/echo >> $@
	/bin/echo "$(TOOLRUN_PFX)$< \"\$$@\"" >> $@
	chmod +x $@


$(MLLEX)0: $(MLLEX_PFX)/mllex.o
	$(POLYCC) -o $@ $<


$(MLLEX_PFX)/mllex.o: $(MLLEX_PFX)/poly-mllex.ML $(MLLEX_PFX)/mllex.ML
	MLLEX_PFX=$(MLLEX_PFX) $(POLY) < $<

else
$(error Can only cope with SML_COMPILER as "poly" or "mlton")


endif

#
# clean targets
#
.PHONY: mllex_clean

clean: mllex_clean
cparser_clean: mllex_clean

mllex_clean:
	-/bin/rm -f $(MLLEX_PFX)/mllex.o $(MLLEX_PFX)/mllex

endif
