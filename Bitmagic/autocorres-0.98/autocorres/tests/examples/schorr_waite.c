/*
 * Copyright (C) 2014, National ICT Australia Limited. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *  * Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *  * Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 *  * The name of National ICT Australia Limited nor the names of its
 *    contributors may be used to endorse or promote products derived from
 *    this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef COMPILE
#define NULL ((void*)0)
#endif

struct node {
  struct node *l, *r;
  unsigned m, c;
};

/* This is Mehta & Nipkow's version of the algorithm (HOL/Hoare/SchorrWaite.thy). */
void schorr_waite(struct node *root) {
  struct node *t = root, *p = NULL, *q;
  while (p != NULL || (t != NULL && !t->m)) {
    if (t == NULL || t->m) {
      if (p->c) {
        q = t; t = p; p = p->r; t->r = q;
      } else {
        q = t; t = p->r; p->r = p->l; p->l = q; p->c = 1;
      }
    } else {
      q = p; p = t; t = t->l; p->l = q; p->m = 1; p->c = 0;
    }
  }
}


/*
 * An executable specification for graph traversal.
 */
void simple_traverse(struct node *n) {
  if (n == NULL || n->m) {
    return;
  }

  n->m = 1;
  simple_traverse(n->l);
  simple_traverse(n->r);
}

#ifdef COMPILE
#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include <time.h>

void make_graph(unsigned size, unsigned graph[size][2], struct node n[size]) {
  for (unsigned i = 0; i < size; ++i) {
    if (graph[i][0] == size) {
      n[i].l = NULL;
    } else {
      n[i].l = &n[0] + graph[i][0];
    }
    if (graph[i][1] == size) {
      n[i].r = NULL;
    } else {
      n[i].r = &n[0] + graph[i][1];
    }
    n[i].c = n[i].m = 0;
  }
}

int main(void) {
  const unsigned max_size = 1000;
  unsigned graph[max_size][2];

  struct timeval tv;
  if (gettimeofday(&tv, NULL)) {
    return 1;
  }
  unsigned long long t = (unsigned long long)tv.tv_sec * 1000000 + tv.tv_usec;
  const int seed = (t >> 32) ^ t;

  srand(seed);
  unsigned size = rand() % max_size + 1;
  for (unsigned i = 0; i < size; ++i) {
    graph[i][0] = rand() % (size+1);
    graph[i][1] = rand() % (size+1);
  }

  struct node n1[max_size], n2[max_size];
  make_graph(size, graph, n1);
  make_graph(size, graph, n2);

  schorr_waite(n1);
  simple_traverse(n2);

  for (unsigned i = 0; i < size; ++i) {
    if (graph[i][0] == size) {
      assert(n1[i].l == NULL);
      assert(n2[i].l == NULL);
    } else {
      assert(n1[i].l == n1 + graph[i][0]);
      assert(n2[i].l == n2 + graph[i][0]);
    }
    if (graph[i][1] == size) {
      assert(n1[i].r == NULL);
      assert(n2[i].r == NULL);
    } else {
      assert(n1[i].r == n1 + graph[i][1]);
      assert(n2[i].r == n2 + graph[i][1]);
    }
    assert(n1[i].m == n2[i].m);
  }

  return 0;
}
#endif
