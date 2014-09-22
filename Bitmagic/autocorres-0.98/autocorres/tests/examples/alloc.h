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

#ifndef _ALLOC_H_
#define _ALLOC_H_

#ifndef NULL
#define NULL ((void *)0)
#endif

/* System word size. */
typedef unsigned long word_t;

/*
 * Allocator memory node.
 *
 * Used as a node in a linked list tracking free memory regions.
 */
struct mem_node {
    word_t size;
    struct mem_node *next;
};

/*
 * Heap object.
 *
 * Contains a pointer to the first node in the chain, and also keeps
 * track of the number of allocations performed, so we know when the
 * entire heap is free.
 */
struct heap {
    word_t num_allocs;
    struct mem_node *head;
};

/* Minimum granuality of the allocator (log2 of number of bytes). */
#define ALLOC_CHUNK_SIZE_BITS 3

/* Minimum alignment that the allocator will return. */
#define DEFAULT_ALIGNMENT_BITS 3

void *alloc(struct heap *heap, word_t size, word_t alignment_bits);

void dealloc(struct heap *heap, void *ptr, word_t size);

void add_mem_pool(struct heap *heap, void *ptr, word_t size);

void init_allocator(struct heap *init_heap, struct mem_node *init_mem_node);

#endif /* _ALLOC_H_ */
