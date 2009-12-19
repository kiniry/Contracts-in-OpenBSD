/*	$OpenBSD: strchr.c,v 1.4 2007/11/25 18:25:34 deraadt Exp $	*/

/*
 * Copyright (c) 2004 Daniel Hartmeier
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *    - Redistributions of source code must retain the above copyright
 *      notice, this list of conditions and the following disclaimer.
 *    - Redistributions in binary form must reproduce the above
 *      copyright notice, this list of conditions and the following
 *      disclaimer in the documentation and/or other materials provided
 *      with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDERS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 */

#include <sys/types.h>
#if !defined(_KERNEL) && !defined(_STANDALONE)
#include <string.h>
#else
#include <lib/libkern/libkern.h>
#define NULL	((char *)0)
#endif

// Proven by Simplify
// Doc Bug ? : The terminating NUL character is considered part of the
//     string.  If c is `\0', strchr() locates the terminating `\0'.

/*@ requires valid_string(s);
    assigns \nothing;
    behavior b1:
       assumes c == '\0';
       ensures \result == \null;
    behavior b1:
       assumes strlen(s) == 0;
       ensures \result == \null;
    behavior b1:
		assumes c == '\0' && strlen(s) > 0;
        ensures \exists integer i; 0 <= i < strlen(s) && s[i] == c ==>
		   \forall integer j; 0 <= j < i && s[j] != c ==> \result == s+i;
	    ensures \forall integer i; 0 <= i < strlen(s) && s[i] != c ==> \result == \null;
 */
char *
strchr(const char *s, int c)
{
	//@ ghost char *orig = s;
	/*@ loop assigns s;
		loop invariant \valid(s);
		loop invariant \base_addr(s) == \base_addr(orig);
		loop invariant 0 <= (s-orig) <= strlen(orig);
		loop invariant \forall integer k; 0 <= k < (s-orig) ==> orig[k] != 0;
		loop invariant \forall integer k; 0 <= k < (s-orig) ==> orig[k] != c;
		loop invariant orig[(s-orig)] == c ==> \forall integer k; 0 <= k < (s-orig) ==> orig[k] != c;
	 */
	while (*s) {
		if (*s == c)
			return ((char *)s);
		s++;
	}
	//@ assert \forall integer k; 0 <= k < strlen(orig) ==> orig[k] != c;
	return (NULL);
}

