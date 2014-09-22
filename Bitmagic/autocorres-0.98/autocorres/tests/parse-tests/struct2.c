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

struct s {
    unsigned long x;
};

struct word_struct {
        unsigned long words[2];
};

struct sc {
    struct s cap;
    struct word_struct ws;
};

static inline unsigned __attribute__((__const__))
    bb(struct word_struct word_struct) {
        return (word_struct.words[0] & 0xfffffff8) << 0;
    }

static inline struct s __attribute__((__const__))
    cncn(void) {
        struct s x;
        x.x = 0;
        return x;
    }

static inline unsigned __attribute__((__const__))
    aa(struct word_struct word_struct) {
            return (word_struct.words[1] & 0xfffffff8) << 0;
    }

static inline void
ff(struct word_struct *mdb_node_ptr, unsigned v) {
        mdb_node_ptr->words[1] &= ~0xfffffff8;
            mdb_node_ptr->words[1] |= (v >> 0) & 0xfffffff8;
}

static inline struct word_struct __attribute__((__const__))
    cc(struct word_struct word_struct, unsigned v) {
            word_struct.words[0] &= ~0xfffffff8;
                word_struct.words[0] |= (v >> 0) & 0xfffffff8;
                    return word_struct;
    }

static inline void
ee(struct word_struct *mdb_node_ptr, unsigned v) {
        mdb_node_ptr->words[0] &= ~0xfffffff8;
            mdb_node_ptr->words[0] |= (v >> 0) & 0xfffffff8;
}

static inline struct word_struct
mk_word_struct(unsigned long a, unsigned long b, unsigned long c, unsigned long d) {
    struct word_struct w;

    w.words[0] = 0;
    w.words[1] = 0;
    w.words[1] |= (a & 0xfffffff8);
    w.words[1] |= (b & 0x1) << 1;
    w.words[1] |= (c & 0x1);
    w.words[0] |= (d & 0xfffffff8);

    return w;
}


void
do_call(struct s newCap, struct sc *s, struct sc *d) {
    struct word_struct the_ws;
    unsigned pp, np;
    ; ;
    the_ws = s->ws;
    d->cap = newCap;
    s->cap = cncn();
    d->ws = the_ws;
    s->ws = mk_word_struct(0, 0, 0, 0);

    pp = bb(the_ws);
    if(pp)
        ff(&((struct sc *)(pp))->ws, ((unsigned int)d));

    np = aa(the_ws);
    if(np)
        ee(&((struct sc *)(np))->ws, ((unsigned int)d));
}


