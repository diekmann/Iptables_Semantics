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

/*
 * AutoCorres simplification of compound expressions.
 * 
 * In C, each of the boolean expressions below is simple.
 * However, C-parser needs to generate a guard for some subexpressions,
 * and so it turns each expression into a complicated statement.
 * 
 * One way to simplify them is by rewriting each expression into the form
 *   guard G; <use expr>
 * where G contains all the necessary guards for the expr.
 * 
 * This makes it easier, for example, for the user to separate
 * the correctness and definedness qualities of the generated code.
 * 
 * Currently, AutoCorres can do this simplification in some cases,
 * but cannot simplify any of the expressions below.
 */
#define NULL ((void*)0)

void f1(int *p) {
  if (p != NULL && *p == 0) *p = 1;
}

struct ure {
  int n;
};

void f2(struct ure *p) {
  if (p != NULL && p->n == 0) p->n = 1;
}

void fancy(int *p) {
  if (p != NULL && (p[0] == 0 || p[1] == 0)) {
    p[0] = p[1];
  }
}

void loop(int *p) {
  while (p != NULL && *p == 0) {
    p++;
  }
}

int arith(int x, int y) {
  return x / y == 0 || y / x == 0;
}
