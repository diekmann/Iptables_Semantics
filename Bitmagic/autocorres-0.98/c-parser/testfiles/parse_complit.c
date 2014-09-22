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

struct foo { int x, y; };

struct bar { struct foo f; char c[3]; int a[6]; };

int simple1(void)
{
  struct foo s = {1,2};
  return s.x;
}

int simple2(void)
{
  struct foo s = {.y = 2};
  return s.x;
}

int simple3(void)
{
  int array[10] = {1,2,3};
  return array[1];
}

int simple4(void)
{
  int array[10] = {[1] = 4, [6] = 7,};
  return array[6];
}

int simple5(void)
{
  char carr[5] = {1};
}

struct bar f(int i)
{
  return (struct bar){.f = {.y = i, .x = i+1,}, .c = {1,[2] = 2}};
}

int g(int j)
{
  struct bar b = {1,2,3,4,5};
  return b.c[1]; // should be 4
}

int h(void)
{
  int array[10] = {[4] = 10,[5] = 10};
  return array[0]; // returns 0
}

int function(void)
{
  struct foo record = {.x = 3,};
  return record.x;
}

int function2(void)
{
  struct bar b = { .f.x = 3, 1,2 };
  return b.f.x; // returns 3
}

int function3(void)
{
  int a[5] = {1,2,3,4,5,[1] = 10};
  return a[1];
}

int main(int argc, char**argv)
{
  struct foo f = {10,12};
  struct bar test = {f,{1,2},{101}}, test2 = {{1}, {2}, {3}};
  struct bar b_array[10] = { test, test2, 1, 2 };
  int aa[] = {1,2,3,[10] = 6};
  return b_array[2].f.x + b_array[0].c[2] + b_array[1].c[0]; // returns 3
}

struct sjwbar {
  int words[1];
};
typedef struct sjwbar bar_t;

int sjw(int sj_w)
{
  bar_t w = { .words = {sj_w} };
}

enum anenum { val1, val2 = -1 };

struct inc_enum {
  enum anenum e;
  int x;
};

int enum_test(int x)
{
  struct inc_enum s = { .x = 3 }, t = { .e = val2 };
  return t.e;
}
