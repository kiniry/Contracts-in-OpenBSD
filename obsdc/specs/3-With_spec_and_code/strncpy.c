/*	$OpenBSD: strncpy.c,v 1.6 2005/08/08 08:05:37 espie Exp $	*/

/*-
 * Copyright (c) 1990 The Regents of the University of California.
 * All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Chris Torek.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#if !defined(_KERNEL) && !defined(_STANDALONE)
#include <string.h>
#else
#include <lib/libkern/libkern.h>
#endif

/*
 * Copy src to dst, truncating or null-padding to always copy n bytes.
 * Return dst.
 */

// Proven by Simplify.

//man: what happens if dst is shorter?
// ? had to add < int_max for safety: overflow.
//param n different in man

/*@ requires valid_string(dst);
    requires valid_string(src);
    requires n < INT_MAX;
    requires \valid_range(dst, 0, minimum(n, strlen(src)));
    ensures \result == dst;
    behavior b1:
		assumes n == 0 || strlen(src) == 0;
		assigns \nothing;
	behavior b2:
		assumes n > 0 && strlen(src) > 0;
		assigns dst[0..n];
		ensures \forall integer i; 0 <= i < minimum(n, strlen(src)) ==> dst[i] == \old(src[i]);
	behavior b3:
		assumes n > 0 && strlen(src) > 0 && strlen(src) <= n;
		assigns dst[0..n];
		ensures \forall integer i; 0 <= i < minimum(n, strlen(src)) ==> dst[i] == \old(src[i]);
		ensures \forall integer i; strlen(src) <= i <= n && dst[i] == '\0';
 */
char *
strncpy(char *dst, const char *src, size_t n)
{
	if (n != 0) {
		char *d = dst;
		const char *s = src;
		//@ ghost int i = 0;
		//@ ghost int origN = n;
		//@ ghost int src_len = strlen(src);
		//@ ghost int origND = n - 1;
		/*@ loop assigns d, s, n, dst[0..origND];
		    loop invariant n >=0;
			loop invariant i <= origN && i <= src_len;
			loop invariant valid_string(d) && valid_string(s);
			loop invariant \forall integer k; 0 <= k < i ==> dst[k] == src[k];
		*/
		do {
			if ((*d++ = *s++) == 0) { //@ ghost i++;
				/* NUL pad the remaining n-1 bytes */
				//@ ghost int j = i;
				/*@ loop assigns d, n, dst[src_len..origND];
					loop invariant n >= 0 && j <= origN;
					loop invariant \forall integer k; src_len <= k < j ==> dst[k] == 0;
				*/
				while (--n != 0)
					*d++ = 0; //@ ghost j++;
				break;
			}
		} while (--n != 0);
	}
	return (dst);
}
