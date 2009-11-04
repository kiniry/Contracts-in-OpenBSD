/*	$OpenBSD: strncat.c,v 1.5 2005/08/08 08:05:37 espie Exp $ */
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

#include <string.h>

/*
 * Concatenate src on the end of dst.  At most strlen(dst)+n+1 bytes
 * are written at dst (at most n+1 bytes being appended).  Return dst.
 */

// Proven by Simplify.

// man params don't match.

/*@
  requires valid_string(src) && valid_string(dst) && \valid_range(dst, 0, strlen(dst) + minimum(n, strlen(src)));
  assigns dst;
  ensures \result == dst;
  behavior b1:
	  assumes n == 0 || strlen(src) == 0;
	  assigns \nothing;
  behavior b2:
      assumes n > 0 && strlen(src) > 0;
	  ensures strlen(dst) == \old(strlen(dst)) + minimum(n, strlen(src));
	  ensures \forall integer k; 0 <= k < \old(strlen(dst)) ==> dst[k] == \old(dst[k]);
	  ensures \forall integer k; 0 <= k < minimum(n, strlen(src)) ==>
			dst[k + \old(strlen(dst))] == src[k];
	  ensures dst[strlen(dst)] == '\0';
 */
char *
strncat(char *dst, const char *src, size_t n)
{
	if (n != 0) {
		//@ghost int lenSrc = strlen(src);
		//@ghost int lenDst = strlen(dst);
		char *d = dst;
		const char *s = src;
		/*@ loop assigns d;
		  @ loop invariant valid_string(d) && (d - dst) <= lenDst;
		  @ loop invariant \forall integer i; 0 <= i < (d-dst) ==> dst[i] != 0;
		 */
		while (*d != 0)
			d++;
		//@ ghost char *ps = d;
		//@ ghost int it = 0;
		//@ ghost int origN = n;
		//@ assert *d == 0;
		/*@ loop assigns d, s, n;
		  @ loop invariant valid_string(d) && valid_string(s);
		  @ loop invariant n > 0;
		  @ loop invariant (s-src) == it;
		  @ loop invariant (d-ps) == it;
		  @ loop invariant 0 <= it < minimum(origN, lenSrc);
		  @ loop invariant \forall integer i; 0 <= i < it ==> dst[lenDst + i] == src[i];
		 */
		do {
			if ((*d = *s++) == 0) //@ ghost it++;
				break;
			d++;
		} while (--n != 0);
		*d = 0;
		//@ assert (d-dst) == lenDst +  minimum(origN, lenSrc);
		//@ assert strlen(dst) == lenDst +  minimum(origN, lenSrc);
	}
	return (dst);
}
