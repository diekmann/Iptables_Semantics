  SML_COMPILER ?= mlton
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

# note this makefile will not work entirely correctly if invoked in the local
# directory; make really needs to be invoked in the parent directory, or
# further up still

STP_PFX := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))


ifndef STP_INCLUDED
STP_INCLUDED=true

STPARSER=$(STP_PFX)/c-parser

.PHONY: stp_all standalone-cparser standalone-tokenizer
standalone-cparser stp_all: $(STPARSER)
standalone-tokenizer: $(STP_PFX)/tokenizer

all: stp_all


STP_CLEAN_TARGETS := $(STP_PFX)/c-parser $(STP_PFX)/c-parser.o  $(STP_PFX)/tokenizer



ifeq ($(SML_COMPILER),mlton)
#
# compilation if the compiler is mlton
#
PARSER_DEPS := $(shell mlton -stop f $(STP_PFX)/c-parser.mlb)
TOKENIZER_DEPS := $(shell mlton -stop f $(STP_PFX)/tokenizer.mlb)


$(STPARSER): $(PARSER_DEPS)
	mlton $<

$(STP_PFX)/tokenizer: $(TOKENIZER_DEPS)
	mlton $<

else ifeq ($(SML_COMPILER),poly)

PARSER0_DEPS := $(shell perl -e 'use Cwd "abs_path"; while (<>) { if (/ml$$|sig$$/i && !/^ *mlton/) { tr/ //d; print abs_path("$(STP_PFX)/$$_"); }}' < $(STP_PFX)/c-parser.mlb)
PARSER_DEPS := $(PARSER0_DEPS) $(realpath $(STP_PFX)/c-parser.mlb) $(STP_PFX)/table.ML

TOKENIZER0_DEPS := $(shell perl -e 'use Cwd "abs_path"; while (<>) { if (/ml$$|sig$$/i && !/^ *mlton/) { tr/ //d; print abs_path("$(STP_PFX)/$$_"); }}' < $(STP_PFX)/tokenizer.mlb)
TOKENIZER_DEPS := $(TOKENIZER0_DEPS) $(realpath $(STP_PFX)/tokenzier.mlb) $(STP_PFX)/table.ML

$(STPARSER): $(STP_PFX)/c-parser.o $(LIBPOLYML)
	$(POLYCC) -o $@ $<

$(STP_PFX)/c-parser.o: $(STP_PFX)/poly-cparser.ML $(PARSER_DEPS)
	STP_PFX=$(STP_PFX) $(POLY) < $<

$(STP_PFX)/tokenizer: $(STP_PFX)/tokenizer.o $(LIBPOLYML)
	$(POLYCC) -o $@ $<

$(STP_PFX)/tokenizer.o: $(STP_PFX)/poly-tokenizer.ML $(TOKENIZER_DEPS)
	STP_PFX=$(STP_PFX) $(POLY) < $<


.PHONY: stp_deps
stp_deps:
	@echo $(PARSER_DEPS)

else
$(error Can only cope with SML_COMPILER as "poly" or "mlton"; got $(SML_COMPILER))

endif

clean: stp_clean

stp_clean:
	-/bin/rm -f $(STP_CLEAN_TARGETS)

endif
