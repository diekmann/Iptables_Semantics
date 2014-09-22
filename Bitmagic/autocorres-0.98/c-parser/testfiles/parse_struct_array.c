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

#define MAX_SIZE 1024

int globint1, globint2, globintarray[3];

struct s {
  int sz;
  char data[MAX_SIZE];
};

struct s_dataptr {
  int sz;
  char *dataptr;
};

int f(struct s* ptr)
{
  return ptr ? 0 : ptr->sz;
}

struct t {
  int x, y;
};

struct u {
  struct t array[10];
};

struct k {
  unsigned short b;
  char c[1];
};

int g(struct u* uptr, int n, struct k *kptr)
{
  return uptr->array[n].x + (kptr ? kptr->b : 0);
}

struct u globu;
struct k globk1, globk2, globkarray[10];

int h(int *i)
{
  globk2.b++;
  return *i + g(&globu, *i * 2, &globk1);
}

int h1(void)
{
  return g(&globu, 2, globkarray + 6);
}

int j(void)
{
  int i = h(&globint1), j = h(globintarray + 2);
  return i + j;
}

int ts20110511_1(struct s *sptr, int i, int shift)
{
  return ((sptr->data[i]) >> shift);
}

int ts20110511_2(struct s *sptr, int shift)
{
  return ((sptr->sz) >> shift);
}

