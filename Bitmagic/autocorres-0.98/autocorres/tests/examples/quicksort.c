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
#ifdef TEST
#include <stdio.h>
#include <stdlib.h>
#endif

unsigned int partition(unsigned int *a, unsigned int n)
{
   // assume n != 0

   // unsigned int pivot = a[0];
   unsigned int pivot_idx = 0; // stupid pivot choice for now

   for (unsigned int i = 1; i < n; i++) {
      if (a[i] < a[pivot_idx]) {
         unsigned int pivot = a[pivot_idx];
         a[pivot_idx] = a[i];
         pivot_idx++;
         a[i] = a[pivot_idx];
         a[pivot_idx] = pivot;
         // pivot = pivot; // hack to get AutoCorres to recognise "pivot" in the loop body
      }
   }

   return pivot_idx;
}

void quicksort(unsigned int *a, unsigned int n)
{
   if (n > 1) {
      unsigned int pivot_idx = partition(a, n);
      quicksort(a, pivot_idx);
      quicksort(a + pivot_idx + 1, n - pivot_idx - 1);
   }
}

#ifdef TEST

int main(void)
{
   unsigned int sz;
   scanf("%u", &sz);
   unsigned int *a = malloc(sz * sizeof(unsigned int));
   for (unsigned int i = 0; i < sz; i++) {
      scanf("%u", a+i);
   }

   quicksort(a, sz);

   for (unsigned int i = 0; i < sz; i++) {
      if (i) putchar(' ');
      printf("%u", a[i]);
   }
   printf("\n");

   return 0;
}

#endif
