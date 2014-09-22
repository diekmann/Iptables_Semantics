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

void f(int i)
{
  int j;
  if (i && 10/i > 2) j = i + 1;
}

int deref(int *p)
{
  return *p;
}

int test_deref(int *p)
{
  if (p && deref(p) > 3) return 4;
  else return 0;
}

int imm_deref(int *p)
{
  if (p && *p > 4) return 4;
  else return 0;
}

int simple(int i)
{
  return (i > 4) && (i < 10);
}

struct foo {
  int data;
};

int condexp(int i, char *ptr, struct foo *ptr2)
{
  int j = i > 0 ? i - 1 : 3;
  char *p = 0 < j && simple(j) ? ptr : 0;
  int k = p ? *p : 10;
  struct foo p2prime = ptr2 ? *ptr2 : (struct foo){.data = 4};
  return j + k + p2prime.data;
}
