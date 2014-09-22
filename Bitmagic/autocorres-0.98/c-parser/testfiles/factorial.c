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

/** FNSPEC alloc_spec:
  "\<forall>\<sigma> k. \<Gamma> \<turnstile>
    \<lbrace>\<sigma>. (free_pool k)\<^bsup>sep\<^esup> \<rbrace>
    \<acute>ret__ptr_to_unsigned :== PROC alloc()
    \<lbrace> ((\<lambda>p s. if k > 0 then (\<turnstile>\<^sub>s p \<and>\<^sup>* \<turnstile>\<^sub>s (p +\<^sub>p 1) \<and>\<^sup>*
        free_pool (k - 1)) s else (free_pool k) s \<and> p = NULL) \<acute>ret__ptr_to_unsigned)\<^bsup>sep\<^esup> \<rbrace>"
*/

unsigned int *alloc(void)
{
  /* Stub */
}

/** FNSPEC free_spec:
  "\<forall>\<sigma> k. \<Gamma> \<turnstile>
    \<lbrace>\<sigma>. (sep_cut' (ptr_val \<acute>p) (2 * size_of TYPE(word32)) \<and>\<^sup>* free_pool k)\<^bsup>sep\<^esup> \<rbrace>
    PROC free(\<acute>p)
    \<lbrace> (free_pool (k + 1))\<^bsup>sep\<^esup> \<rbrace>"
*/

void free(unsigned int *p)
{
  /* Stub */
}

/** FNSPEC factorial_spec:
  "\<forall>\<sigma> k. \<Gamma> \<turnstile>
    \<lbrace>\<sigma>. (free_pool k)\<^bsup>sep\<^esup> \<rbrace>
    \<acute>ret__ptr_to_unsigned :== PROC factorial(\<acute>n)
    \<lbrace> if \<acute>ret__ptr_to_unsigned \<noteq> NULL then (sep_fac_list \<^bsup>\<sigma>\<^esup>n \<acute>ret__ptr_to_unsigned \<and>\<^sup>*
          free_pool (k - (unat \<^bsup>\<sigma>\<^esup>n + 1)))\<^bsup>sep\<^esup> \<and> (unat \<^bsup>\<sigma>\<^esup>n + 1) \<le> k else (free_pool k)\<^bsup>sep\<^esup> \<rbrace>"
*/

unsigned int *factorial(unsigned int n)
{
  unsigned int *p, *q;

  if (n == 0) {
    p = alloc();

    if (!p)
      return 0;

    *p = 1;
    *(p + 1) = 0;

    return p;
  }

  q = factorial(n - 1);

  if (!q)
    return 0;

  p = alloc();

  if (!p) {
    while (q)
      /** INV: "\<lbrace> \<exists>xs. (sep_list xs \<acute>q \<and>\<^sup>* free_pool (k - length xs))\<^bsup>sep\<^esup> \<and>
                   length xs \<le> k \<rbrace>" */
    {
      unsigned int *k = (unsigned int *)*(q + 1);

      free(q);
      q = k;
    }

    return 0;
  }

  *p = n * *q;
  *(p + 1) = (unsigned int)q;

  return p;
}
