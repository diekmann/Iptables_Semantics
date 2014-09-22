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

struct struct1 {
  char c;
  int fld1;
  char fld2;
};

struct charpair {
  char c1;
  char c2;
};

struct allinclusive {
  char c;
  struct charpair p1;
  struct struct1 s;
  int foo;
  };

int firstinc_ptr(struct struct1 *sptr)
{
  if (sptr) { return sptr->fld1 + 1; }
  else return 1;
}

int firstinc(struct struct1 m)
{
  return m.fld1 + 1;
}

struct struct1 *firstptr_ptr(struct struct1 *sptr)
{
  return sptr + 1;
}

int *fldaddr(struct struct1 *sptr)
{
  return &(sptr->fld1);
}

struct allinclusive mkall(int i)
{
  struct allinclusive s;
  s.c = i;
  s.s.c = i + 1;
  s.p1.c1 = i + 2;
  s.p1.c2 = i + 3;
  s.s.fld1 = i + 4;
  s.s.fld2 = i + 5;
  s.foo = i + 6;
  return s;
}


struct voidstar {
  void *vptr;
  int i;
};

struct recursive1;
struct recursive2 {
  struct recursive1 *ptr;
  int fld;
};

struct recursive1 {
  struct recursive2 subfld;
  char c;
};

struct {
  int anonfld1;
  char anonfld2[10];
} anon_global1, anon_global2;

int f(int i)
{
  if (i == 0) return anon_global1.anonfld1;
  else return anon_global2.anonfld1;
}

struct tree20 {
  struct tree20 *array[20];
  void *data;
};

struct tree20 create20(void *init)
{
  struct tree20 s;
  for (int i = 0; i < 20; i++) s.array[i] = 0;
  s.data = init;
  return s;
}

typedef struct monstrous {
  int i,j;
} __attribute__((packed)) monstrous_t;

monstrous_t yikes(void)
{
  return (monstrous_t){.j = 6, .i = 3};
}
