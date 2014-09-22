/*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions, and the following disclaimer,
 *    without modification.
 *
 * 2. Redistributions in binary form must reproduce at minimum a disclaimer
 *    substantially similar to the "NO WARRANTY" disclaimer below
 *    ("Disclaimer") and any redistribution must be conditioned upon
 *    including a substantially similar Disclaimer requirement for further
 *    binary redistribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTIBILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDERS OR CONTRIBUTORS BE LIABLE FOR SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
 * THE POSSIBILITY OF SUCH DAMAGES.
 */

int zuzu = 1;
int zozo = 1;
int zyzy = 1;

int incz(void) {
    zuzu = zuzu + 1;
    return zuzu;
}

int incp(void) {
    int *pp = &zozo;

    *pp = *pp + 1;
    return *pp;
}

/*
    This gives a global record:
	[|
	   global_exn_var_';
	   t_hrs_';
	   phantom_machine_state_';
	   zuzu_';
	   ...
	|]
    Note:
    * The program reads and writes zuzu but does not take its address.
      ==> There is an explicit field for zuzu.

    * The program takes the address of zozo.
      ==> There is not an explicit field for zozo
      ==> It is instead modelled in t_hrs_' (see below)

    * The program does not write to zyzy.
      ==> There is not an explicit field for zyzy.
      ==> Nor is it modelled in t_hrs_'
      ==> It does exist as a constant: zyzy == 1

    * t_hrs_' stands for "typed heap representation structure"
      It is a function from addresses to bytes and type tags (which say how
      those bytes are to be interpreted), as described in "Types, Bytes,
      and Separation Logic".
      A variable must be modelled in the heap, to account for the effects
      of aliasing, whenever the address-of (&) operator is used against it.
 */

