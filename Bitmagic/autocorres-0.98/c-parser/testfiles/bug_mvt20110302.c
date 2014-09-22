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

typedef unsigned long uint32_t;
typedef uint32_t vptr_t;

struct cap {
    uint32_t words[2];
};
typedef struct cap cap_t;

struct mdb_node {
    uint32_t words[2];
};
typedef struct mdb_node mdb_node_t;

struct create_ipcbuf_frame_ret {
    cap_t  ipcbuf_cap;
    vptr_t ipcbuf_vptr;
};
typedef struct create_ipcbuf_frame_ret create_ipcbuf_frame_ret_t;

create_ipcbuf_frame_ret_t
create_ipcbuf_frame(void)
{
    cap_t  cap;
    vptr_t vptr;
    /* If I comment out the line below, it works! */
    return (create_ipcbuf_frame_ret_t){ cap, vptr };
}

/* And if I only comment out the completely unrelated struct */
/* below (and keep the line above), it works as well!        */
struct cte {
    cap_t cap;
    mdb_node_t cteMDBNode;
};
