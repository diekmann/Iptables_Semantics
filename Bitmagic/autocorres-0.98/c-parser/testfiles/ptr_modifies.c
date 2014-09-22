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

typedef unsigned long uint32_t;

struct foo {
    uint32_t words[1];
};
typedef struct foo foo_t;

/** FNSPEC
  f_spec: "\<forall>i. \<Gamma> \<turnstile> \<lbrace> \<acute>i = i \<rbrace> \<acute>ret__unsigned :== PROC f(\<acute>i) \<lbrace> \<acute>ret__unsigned = i + 1 \<rbrace>"
*/
unsigned f(unsigned i)
{
  return (3 / i ? i+1 : i);
}


static inline void __attribute__((__pure__))
foo_ptr_new(foo_t *foo_ptr, uint32_t bar) {
  foo_ptr->words[0] = f(0);

  foo_ptr->words[0] |= bar << 0;
}

unsigned g(unsigned i)
{
  return f(i) + 3;
}

struct thing {
  int *base;
  int size;
};
typedef struct thing thing_t;

int h(thing_t t)
{
  for (int i = 0; i < t.size; i++) {
    t.base[i] = 0;
  }
  return t.size;
}


