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

#define SQRT_UINT_MAX 65536

/*
 * Determine if the given number 'n' is prime.
 *
 * We return 0 if 'n' is composite, or non-zero if 'n' is prime.
 */
unsigned is_prime_linear(unsigned n)
{
    /* Numbers less than 2 are not prime. */
    if (n < 2)
        return 0;

    /* Find the first non-trivial factor of 'n'. */
    for (unsigned i = 2; i < n; i++) {
        if (n % i == 0)
            return 0;
    }

    /* No factors. */
    return 1;
}

/*
 * Determine if the given number 'n' is prime.
 *
 * We return 0 if 'n' is composite, or non-zero if 'n' is prime.
 *
 * Faster version that 'is_prime'; runs in O(sqrt(n)).
 */
unsigned int is_prime(unsigned int n)
{
    /* Numbers less than 2 are not primes. */
    if (n < 2)
        return 0;

    /* Find the first non-trivial factor of 'n' or sqrt(UINT_MAX), whichever
     * comes first. */
    /* Find the first non-trivial factor of 'n' less than sqrt(n). */
    for (unsigned i = 2; i < SQRT_UINT_MAX && i * i <= n; i++) {
        if (n % i == 0)
            return 0;
    }

    /* No factors. */
    return 1;
}

