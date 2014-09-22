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

/* also tests
   - post-increment and decrement (which are common in for loops)
   - arrays on the heap and stack (treated differently in VCG-land)
*/

int *f(int *i, int c)
{
  unsigned j;
  for (j = 0; j < 4; j++) i[j] = i[j] + c;
  i[0]++;
  return i;
}

int g(int c)
{
  for (unsigned int j = 10; 0 < j; j--)
    /** INVARIANT: "\<lbrace> 0 <= \<acute>j & \<acute>j <= 10 \<rbrace>" */
    {
      c = c + j;
    }
  return c;
}

int h(int c)
{
  int a[10];
  for (unsigned int j = 0; j < 10; j++) a[j] = j;
  a[0] = a[1] + a[2];
  return a[0];
}

int f2(int *a)
{
  int j, res;
  for (j=0,res=0; j < 32; j += 4) { res += a[j]; }
  return res;
}
