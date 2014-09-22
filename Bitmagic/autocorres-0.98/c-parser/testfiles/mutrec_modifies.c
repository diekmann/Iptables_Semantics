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

int x,y;

int g(int);
int h(int);

int f(void)
{
  if (x < 0) return 1 + g(6);
  else {
    int i = h(x);
    return 7 + i;
  }
}

int g(int i)
{
  x++;
  int local = f();
  return i + local;
}

int h(int i)
{
  y++;
  return i * 2 + y;
}

int atop(int i)
{
  if (i < 0) return g(i);
  else return 3;
}

int fact(int i)
{
  if (i < 2) return 1;
  else return i * fact(i - 1);
}


void rec2(void);
void rec3(void);
void rec4(void);
int rec1(void)
{
  if (x < 0) rec2();
  return 1;
}

void rec2(void)
{
  if (y > x) rec1(); else rec4();
}

void rec3(void)
{
  int tmp = h(x);
  if (x > tmp) rec2();
}

void rec4(void)
{
  rec2();
  rec3();
}


  
