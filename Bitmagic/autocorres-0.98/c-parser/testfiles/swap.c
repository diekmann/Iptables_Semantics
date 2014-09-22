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

/** FNSPEC swap_spec:
  "\<forall>x y. \<Gamma> \<turnstile> 
    \<lbrace>\<sigma>. (\<acute>p \<mapsto> x \<and>\<^sup>* \<acute>q \<mapsto> y)\<^bsup>sep\<^esup> \<rbrace> 
      PROC swap(\<acute>p,\<acute>q)
    \<lbrace> (\<^bsup>\<sigma>\<^esup>p \<mapsto> y \<and>\<^sup>* \<^bsup>\<sigma>\<^esup>q \<mapsto> x)\<^bsup>sep\<^esup> \<rbrace>"
*/

void swap(unsigned int *p, unsigned int *q)
{
  unsigned int x;

  x = *p;
  *p = *q;
  *q = x;
}

/** FNSPEC test_spec:
  "\<forall>x y. \<Gamma> \<turnstile> 
    \<lbrace>\<sigma>. (\<acute>a \<mapsto> x \<and>\<^sup>* \<acute>b \<mapsto> y \<and>\<^sup>* \<acute>c \<mapsto> -)\<^bsup>sep\<^esup> \<rbrace> 
      PROC test(\<acute>a,\<acute>b,\<acute>c)
    \<lbrace> (\<^bsup>\<sigma>\<^esup>a \<mapsto> (x + y) \<and>\<^sup>* \<^bsup>\<sigma>\<^esup>b \<mapsto> x \<and>\<^sup>* \<^bsup>\<sigma>\<^esup>c \<mapsto> y)\<^bsup>sep\<^esup> \<rbrace>"
*/

void test(unsigned int *a, unsigned int *b, unsigned int *c)
{
  *c = *a + *b;
  swap(a,b);
  swap(c,a);
}
