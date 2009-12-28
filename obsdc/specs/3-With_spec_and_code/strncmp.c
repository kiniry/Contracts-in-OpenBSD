/*	$OpenBSD: strncmp.c,v 1.7 2005/08/08 08:05:37 espie Exp $	*/

/*
 * Copyright (c) 1989 The Regents of the University of California.
 * All rights reserved.
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

// Proven by z3

// Code change! Bug 306 (fixed in Why 2.2)
// consequently had to take unsigned casts out.

// Param n does not match man.
// n == 0 ==> 0 not mentioned in man.

// had to add n < INT_MAX

/*@  requires valid_string(s1);
     requires valid_string(s2);
     requires n < INT_MAX;
     assigns \nothing;
     behavior b1:
		assumes n == 0;
		ensures \result == 0;
	 behavior b2:
		assumes n > 0;
        assumes \forall integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && s1[i] == s2[i];
        ensures \result == 0;
     behavior b3:
	 	assumes n > 0;
	 	assumes \exists integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && s1[i] != s2[i];
        ensures \exists integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && s1[i] < s2[i] ==> \result < 0 ;
     behavior b4:
	 	assumes n > 0;
	 	assumes \exists integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && s1[i] != s2[i];
        ensures \exists integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && s1[i] > s2[i] ==> \result > 0;
 */
int
strncmp(const char *s1, const char *s2, size_t n)
{
	if (n == 0)
		return (0);
	//@ ghost char *orig1 = s1;
	//@ ghost char *orig2 = s2;
	//@ ghost int origN = n;
	/*@ loop assigns s1, s2, n;
	    loop variant n;
		loop invariant valid_string(orig1);
		loop invariant valid_string(orig2);
		loop invariant \valid(s1) && \valid(s2);
		loop invariant \base_addr(s1) == \base_addr(orig1);
		loop invariant \base_addr(s2) == \base_addr(orig2);
		loop invariant s1-orig1 == s2 - orig2;
		loop invariant 0 <= (s2-orig2) <= strlen(orig2);
		loop invariant 0 <= (s1-orig1) <= strlen(orig1);
		loop invariant \forall integer k; 0 <= k < (s1-orig1) ==> orig1[k] != 0;
		loop invariant \forall integer k; 0 <= k < (s1-orig1)==> orig1[k] == orig2[k];
		loop invariant 0 < n <=  origN;
		loop invariant 0 <= origN - n  <= origN;
	*/
	do {
		if (*s1 != *s2++)
			return (*s1 - *(--s2)); //entered bug 306 : return (*(unsigned char *)s1 - *(unsigned char *)--s2);
		if (*s1++ == 0)
			break; //@assert *(s1-1) == *(s2-1);
	} while (--n != 0);
	return (0);
}
