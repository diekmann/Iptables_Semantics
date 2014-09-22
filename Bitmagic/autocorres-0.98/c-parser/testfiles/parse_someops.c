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

int f(int x, int y, unsigned u, unsigned v)
{
  return (x < y) + (x <= y) + (x >= y) + (x != y) + (u < v);
}

int g(int x, int y)
{
  return (x % y) * (x + y) / (x - y);
}

int condexp(int x, int y)
{
  return x ? y : y + 1;
}

int cbools(int i, int *p)
{
  int j = 10;
  while (j) { i++; j--; }
  return (i || !p) ;
}

int bitwise(int x, int y)
{
  return (x & y) + (x | y) + (x ^ ~y);
}

int shifts(int x, int y)
{
  return (x << y) + (x >> y);
}

char inc(int x)
{
  return x + 1;
}

int callbool(int y)
{
  y = condexp(inc(y) || inc(inc(y*2)), 3);
  return condexp(y > 3, y == 4 || y == 10);
}

int ptr_compare(void *vptr, int *x)
{
  return (x != vptr);
}

int large_literal_rshift (int w)
{
  return 0xF0000000 >> w;
}

void assignops(int *x, int y)
{
  *x >>= y;
  *x <<= y;
  *x += y;
  *x *= y;
  *x /= y;
  *x ^= y;
  *x -= y;
  *x &= y;
  *x |= y;
  *x %= y;
  *x = y;
}
