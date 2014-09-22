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
 * Triggers a bug relating to combinations of complex bit operations
 * and bodiless functions.
 */

void fr(unsigned long a, unsigned long b, unsigned long *c)
        __attribute__((externally_visible))
        __attribute__((__noreturn__));

unsigned long global;

struct word_struct {
        unsigned long words[2];
};

static inline struct word_struct
gen_struct(unsigned long a, unsigned long b, unsigned long c, unsigned long d) {
    struct word_struct w;

    w.words[0] = 0;
    w.words[1] = 0;
    w.words[1] |= (a & 0xfffffff8) >> 0;
    w.words[1] |= (b & 0x1) << 1;
    w.words[1] |= (c & 0x1) << 0;
    w.words[0] |= (d & 0xfffffff8) >> 0;

    return w;
}

void
frw(int x)
{
    if (x) {
        fr(3, 4, &global);
        gen_struct(32, 53, 23, 543);
    } else {
        fr(1, 2, (void *)0);
        gen_struct(1, 2, 3, 4);
    }
}

void call_fr(void)
{
    fr(3, 4, &global);
    fr(3, 4, &global);
}

