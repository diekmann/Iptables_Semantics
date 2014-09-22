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

/* Heap-unliftable functions calling liftable ones and vice versa. */

int f(int x) {
  return x + 1;
}
int g(int x) {
  return g(x + 1);
}

int *call_f(void *mem) {
  /** AUXUPD: "(True, ptr_retyp (ptr_coerce \<acute>mem :: word32 ptr))" */
  *(int*)mem = f(g(*(int*)mem));
}

void rec_untyp(int*);
void rec_typ(void *mem) {
  /** AUXUPD: "(True, ptr_retyp (ptr_coerce \<acute>mem :: word32 ptr))" */
  rec_untyp(mem);
}
void rec_untyp(int *ptr) {
  *ptr = f(g(*ptr));
  /** AUXUPD: "(True, ptr_retyp (ptr_coerce \<acute>ptr :: unit ptr))" */
  rec_typ(ptr);
}

void call_all(void) {
  rec_untyp(call_f(0));
}
