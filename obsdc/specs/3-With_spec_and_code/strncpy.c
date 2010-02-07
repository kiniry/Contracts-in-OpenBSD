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

// Proven by Z3 (b1: 6/6, b2: 9/9, b3: 11/12, default: 86/88 -> missing 2 POs proved by Simplify, Safety: 14/14.

//man: what happens if dst is shorter?
//param n different in man

/*@ requires valid_string(src);
    requires \valid_range(dst, 0, n);
    requires disjoint_strings(dst, src);
    requires disjoint_strings_len(dst, src, n);
    ensures \result == dst;
    behavior b1:
		assumes n == 0;
		assigns \nothing;
	behavior b2:
		assumes n > 0 && strlen(src) >= n;
		assigns dst[..];
		ensures \forall integer i; 0 <= i < n ==> dst[i] == src[i];
	behavior b3:
		assumes n > 0 && strlen(src) < n;
		assigns dst[0..];
		ensures \forall integer i; 0 <= i < strlen(src) ==> dst[i] == src[i];
		ensures \forall integer i; strlen(src) <= i < n ==> dst[i] == 0;
 */
char *
strncpy(char *dst, const char *src, size_t n)
{
	if (n != 0) {
		char *d = dst;
		const char *s = src;
		/*@ loop assigns d, s, n, dst[..];
		    loop invariant \at(n, Pre) >= n > 0;
			loop invariant strlen(src) >= \at(n, Pre) ==> 0 <= d-dst <= \at(n, Pre) <= strlen(src);
			loop invariant strlen(src) >= \at(n, Pre) ==> 0 <= s-src <= \at(n, Pre) <= strlen(src);
			loop invariant strlen(src) >= \at(n, Pre) ==> d-dst == s-src;
			loop invariant strlen(src) < \at(n, Pre) ==> d-dst <= strlen(src) ==> d-dst == s-src;
			loop invariant strlen(src) < \at(n, Pre) ==> 0 <= s-src <= strlen(src) < \at(n, Pre);
			loop invariant strlen(src) < \at(n, Pre) ==> 0 <= d-dst <= strlen(src) < \at(n, Pre);
			loop invariant d-dst == \at(n, Pre) - n;
			loop invariant \base_addr(d) == \base_addr(dst);
			loop invariant \base_addr(s) == \base_addr(src);
			loop invariant \valid(d) && \valid(s);
			loop invariant \valid_range(dst, 0, \at(n, Pre));
			loop invariant \valid_range(src, 0, strlen(src));
			loop invariant strlen(src) >= \at(n, Pre) ==> (\forall integer k; 0 <= k < (d-dst) < \at(n, Pre) ==> dst[k] == src[k]);
			loop invariant strlen(src) < \at(n, Pre) ==> \forall integer k; 0 <= k < (d-dst) ==> dst[k] == src[k];
			loop invariant \forall integer k; 0 <= k < (s-src) <= strlen(src) ==> src[k] != 0;
			loop invariant \forall integer k; 0 <= k <= strlen(src) ==> src[k] == \at(src[k], Pre);
		*/
		do {
			if ((*d++ = *s++) == 0){
				/* NUL pad the remaining n-1 bytes */
				//@ ghost char *p = d;
				//@ ghost size_t n2 = n;
				/*@ loop assigns d, n, dst[p-dst..];
				    loop invariant strlen(src) < \at(n, Pre) ==> \valid(d);
					loop invariant \base_addr(d) == \base_addr(dst);
					loop invariant \base_addr(d) == \base_addr(p);
					loop invariant \at(n, Pre) >= n2 >= n > 0;
					loop invariant 0 <= d - p <= (n2-1);
					loop invariant d - p == n2 - n;
					loop invariant 0 <= d-dst <= \at(n, Pre);
					loop invariant \forall integer k; (p-dst) <= k < (d-dst) ==> dst[k] == 0;
					loop invariant \forall integer k; 0 <= k <= strlen(src) ==> src[k] == \at(src[k], Pre);
					loop invariant \forall integer i; 0 <= i < strlen(src) ==> dst[i] == src[i];
				*/
				while (--n != 0)
					*d++ = 0;
				break;
			}
		} while (--n != 0);
	}
	return (dst);
}
