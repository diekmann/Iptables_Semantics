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

/* http://blog.regehr.org/archives/909 */

long long LONG_MAX = 9223372036854775807L;
long long LONG_MIN = -9223372036854775807L - 1L;

int error = 0;

extern int error;
long str2long(const char *);

long str2long(const char *s) {
    long val = 0;
    int negative = 0;

    if (*s == '-') {
        negative = 1;
        s++;
    }

    if (*s == '\0') {
        error = 1;
        return -1;
    }

    for (;*s != '\0'; s++) {
        if (*s < '0' || *s > '9') {
            /* Non-numeric character; bail out. */
            error = 1;
            return -1;
        } else {
            long d = *s - '0'; /* digit value */

            if (negative) {
                if ((LONG_MIN + d) / 10 > val) {
                    /* We're about to underflow. */
                    error = 1;
                    return -1;
                }
                val = val * 10 - d;
            } else {
                if ((LONG_MAX - d) / 10 < val) {
                    /* We're about to overflow. */
                    error = 1;
                    return -1;
                }
                val = val * 10 + d;
            }
        }
    }
    return val;
}
