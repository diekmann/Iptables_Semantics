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

unsigned global;

int mult(int x, int y)
{
  return x * y;
}

int fact(int n)
{
  int factor, total;
  total = 1;
  factor = 2;
  while (factor <= n)
    /** INV: "\<lbrace> unat \<acute>total = fac (unat \<acute>factor - 1) &
                       \<acute>factor \<le> \<acute>n + 1
              \<rbrace>" */
    {
      total = mult(factor, total);
      factor = factor + 1;
    }
  return total;
}

/** FNSPEC
  g_modifies: "\<forall> \<sigma>. \<Gamma> \<turnstile> {\<sigma>} \<acute>ret__int :== PROC g() {t. t may_not_modify_globals \<sigma>}"
*/
int g(void)
{
  return 257;
}

/** FNSPEC
  f_spec: "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC f(n) \<lbrace> \<acute>ret__int = 1 \<rbrace>"
  f_modifies: "\<forall>\<sigma>. \<Gamma> \<turnstile> {\<sigma>} \<acute>ret__int :== PROC f(\<acute>n)
                       {t. t may_not_modify_globals \<sigma>}"
*/
int f (int n)
{
  char c;
  global++;
  c = g();
  return c;
}


/** FNSPEC
  h_modifies:
    "\<forall> \<sigma>.
       \<Gamma> \<turnstile>
          {\<sigma>}
            \<acute>ret__ptr_to_void :== PROC h()
          {t. t may_not_modify_globals \<sigma>}"
*/
void *h(void)
{
  return 0;
}

/** FNSPEC
  i_modifies: "\<forall> \<sigma>. \<Gamma> \<turnstile> {\<sigma>} \<acute>ret__int :== PROC i() {t. t may_not_modify_globals \<sigma>}"
*/
int i(void)
{
  int *iptr = h();
  return iptr[3];
}

/** FNSPEC
      has_bogus_spec_spec: "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC has_bogus_spec() \<lbrace> \<acute>ret__int = 4 \<rbrace>"
*/
int has_bogus_spec(void)
{
  return 3;
}

int calls_bogus(void)
{
  return has_bogus_spec();
}
