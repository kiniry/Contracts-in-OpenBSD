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

// Proven by Simplify

// Code change! Bug 306 (fixed in Why 2.2)
// Param n does not match man.
// n == 0 ==> 0 not mentioned in man.

/*@  requires valid_string(s1);
  @  requires valid_string(s2);
  @  assigns \nothing;
  @  ensures (n == 0) ==> \result == 0;
  @  ensures \forall integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && s1[i] == s2[i] ==> \result == 0;
  @  ensures \exists integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && (unsigned char)s1[i] < (unsigned char) s2[i] ==> \result < 0;
  @  ensures \exists integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && (unsigned char) s2[i] > (unsigned char)s1[i] ==> \result > 0;
 */
int
strncmp(const char *s1, const char *s2, size_t n)
{
	if (n == 0)
		return (0);
	//@ ghost char *orig1 = s1;
	//@ ghost char *orig2 = s2;
	//@ ghost int len1 = strlen(s1);
	//@ ghost int len2 = strlen(s2);
	//@ ghost int len = n - 1;
	//@ ghost int i = 0;
	/*@ loop assigns s1, s2, n;
		loop invariant n >= 0 && 0 <= i <= minimum(len, minimum(len1, len2));
		loop invariant valid_string(s1) && valid_string(s2);
		loop invariant \forall integer k; 0 <= k < i ==> orig1[k] == orig2[k];
	*/
	do {
		if (*s1 != *s2++)
			return ((unsigned char)*s1 - (unsigned char)*(--s2)); //entered bug 306 : return (*(unsigned char *)s1 - *(unsigned char *)--s2);
		if (*s1++ == 0)
			break;
	} while (--n != 0); //@ ghost i++;
	return (0);
}
