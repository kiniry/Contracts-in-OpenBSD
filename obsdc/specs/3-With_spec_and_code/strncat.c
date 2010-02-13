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

// Proven by Z3 (b1: 5/5, b2: 12/13, b3: 12/13, Default behavior: 78/83 {1 pli for valid d, rest asserts, 1 proved by simplify}.
// safety: 11/14 (d safety, first loop safety ? and the assertions about p after first loop?).
// man params don't match.
/*@
  requires valid_string(src);
  requires valid_string(dst);
  requires \valid_range(dst, 0, strlen(dst) + minimum(n, strlen(src)) + 1);
  requires disjoint_strings(src, dst);
  requires disjoint_strings_len(dst, src, strlen(dst) + strlen(src) + 1);
  requires disjoint_strings_len(dst, src, strlen(dst) + n + 1);
  ensures \result == dst;
  behavior b1:
	  assumes n == 0;
	  assigns \nothing;
  behavior b2:
      assumes n > 0 && strlen(src) <= n;
      assigns dst[..];
	  ensures strlen(dst) == strlen{Old}(dst) + strlen(src);
	  ensures \forall integer k; 0 <= k < strlen{Old}(dst) ==> dst[k] == \old(dst[k]);
	  ensures \forall integer k; 0 <= k < strlen(src) ==>
			dst[k + strlen{Old}(dst)] == src[k];
  behavior b3:
      assumes n > 0  && strlen(src) > n;
      assigns dst[..];
	  ensures strlen(dst) == strlen{Old}(dst) + n;
	  ensures \forall integer k; 0 <= k < strlen{Old}(dst) ==> dst[k] == \old(dst[k]);
	  ensures \forall integer k; 0 <= k < n ==>
			dst[k + strlen{Old}(dst)] == src[k];
 */
char *
strncat(char *dst, const char *src, size_t n)
{
	if (n != 0) {
		char *d = dst;
		const char *s = src;
		/* loop assigns d;
		   loop invariant \base_addr(d) == \base_addr(dst);
		   loop invariant \valid(d);
		   loop invariant \valid_range(dst, 0, strlen{Pre}(dst));
		   loop invariant 0 <= (d - dst) <= strlen{Pre}(dst);
		   loop invariant \forall integer i; 0 <= i < (d-dst) ==> dst[i] != 0;
		   loop invariant \forall integer i; 0 <= i <= strlen{Pre}(dst) ==> dst[i] == \at(dst[i], Pre);
		   loop invariant \forall integer i; 0 <= i <= strlen(src) ==> src[i] == \at(src[i], Pre);
		 */
		while (*d != 0)
			d++;
		//@ assert *d == 0;
		//@ assert d-dst == strlen{Pre}(dst);
		//@ assert d == dst + strlen{Pre}(dst);
		//@ assert \valid_range(d, 0, minimum(n, strlen(src)) + 1);

		/*@ loop assigns d, s, n, dst[..];
		    loop invariant \valid(d);
		    loop invariant (s-src) <= strlen(src) ==> \valid(s);
		    loop invariant \base_addr(d) == \base_addr(dst);
		    loop invariant \base_addr(s) == \base_addr(src);
		    loop invariant \valid_range(dst, 0, strlen{Pre}(dst) + minimum(\at(n, Pre), strlen(src)) + 1);
		    loop invariant \at(n, Pre) >= n > 0;

			loop invariant \at(n, Pre) >= strlen(src) ==> 0 <= (s-src) <= strlen(src);
			loop invariant \at(n, Pre) < strlen(src) ==> 0 <= (s-src) <= \at(n, Pre) < strlen(src);

			loop invariant \at(n, Pre) >= strlen(src) ==> strlen{Pre}(dst) <= (d-dst) <= strlen{Pre}(dst) + strlen(src) <= strlen{Pre}(dst) + \at(n, Pre);
		    loop invariant \at(n, Pre) < strlen(src)  ==> strlen{Pre}(dst) <= (d-dst) <= strlen{Pre}(dst) + \at(n, Pre) < strlen{Pre}(dst) + strlen(src);

		    loop invariant (s-src) <= strlen(src) ==> d - dst - strlen{Pre}(dst) ==  (s - src);
		    loop invariant d - dst - strlen{Pre}(dst) == (\at(n, Pre) - n);

		    loop invariant \forall integer i; strlen{Pre}(dst) <= i < (d-dst) ==> dst[i] == src[i - strlen{Pre}(dst)];
		    loop invariant \forall integer i; 0 <= i < (s-src) <= strlen(src) ==> src[i] != 0;
		    loop invariant \forall integer i; 0 <= i <= strlen(src) ==> src[i] == \at(src[i], Pre);
		    loop invariant \forall integer i; 0 <= i < strlen{Pre}(dst) ==> dst[i] == \at(dst[i], Pre);
		    loop invariant \forall integer i; strlen{Pre}(dst) <= i < (d-dst) ==> dst[i] != 0 ;
		 */
		do {
			if ((*d = *s++) == 0)
				break;
			d++;
		} while (--n != 0);
		*d = 0;
		//@ assert dst[d-dst] == 0;

		//@ assert \at(n, Pre) > strlen(src) ==> *(s-1) == 0;
		//@ assert \at(n, Pre) > strlen(src) ==> strlen(src) == s-src -1;
		//@ assert \at(n, Pre) > strlen(src) ==> strlen(dst) == strlen{Pre}(dst) + s-src -1;
		//@ assert \at(n, Pre) > strlen(src) ==> strlen(dst) == strlen{Pre}(dst) + strlen(src);

		//@ assert \at(n, Pre) < strlen(src) ==> dst[strlen{Pre}(dst) + \at(n, Pre)] == 0;
		//@ assert \at(n, Pre) < strlen(src) ==> d-dst == (strlen{Pre}(dst) + \at(n, Pre)) && *d == 0;
		//@ assert \at(n, Pre) < strlen(src) ==> strlen(dst) == strlen{Pre}(dst) + \at(n, Pre);

		//@ assert \at(n, Pre) == strlen(src) ==> dst[strlen{Pre}(dst) + \at(n, Pre)] == 0;
		//@ assert \at(n, Pre) == strlen(src) ==> d-dst == (strlen{Pre}(dst) + \at(n, Pre)) && *d == 0;
		//@ assert \at(n, Pre) == strlen(src) ==> strlen(dst) == strlen{Pre}(dst) + \at(n, Pre);
	}
	return (dst);
}
