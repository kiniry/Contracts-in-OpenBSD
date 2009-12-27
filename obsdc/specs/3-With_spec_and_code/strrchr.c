/*	$OpenBSD: strrchr.c,v 1.1 2007/11/25 18:25:34 deraadt Exp $	*/

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

// Proven by alt-ergo and z3.

// (doc?) bug: '\0' ==> null.
/*@ requires valid_string(s);
    assigns \nothing;
    behavior b1:
       assumes c == '\0';
       ensures \result == \null;
    behavior b2:
       assumes strlen(s) == 0;
       ensures \result == \null;
    behavior b3:
		assumes c != '\0' && strlen(s) > 0;
        ensures \exists integer i; 0 <= i < strlen(s) && s[i] == c &&
         (\forall integer j; i < j < strlen(s) ==> s[j] != c) ==> \result == s+i;
    behavior b4:
		assumes c != '\0' && strlen(s) > 0;
		assumes \forall integer i; 0 <= i < strlen(s) && s[i] != c;
		ensures \result == \null;
 */
char *
strrchr(const char *s, int c)
{
	char *t = NULL;
	//@ ghost char *orig = s;
	/*@ loop assigns s;
		loop invariant \valid(s);
		loop invariant \base_addr(s) == \base_addr(orig);
		loop invariant 0 <= (s-orig) <= strlen(orig);
		loop invariant \forall integer k; 0 <= k < (s-orig) ==> orig[k] != 0;
		loop invariant \exists integer k; 0 <= k < (s-orig) && orig[k] == c ==> t != \null;
		loop invariant strlen(orig) == 0 ==> t == \null;
		loop invariant c == 0 ==> t == \null;
		loop invariant t == \null || *t == c;
	 */
	while (*s) {
		if (*s == c)
			t = (char *)s;
		s++;
	}
	return (t);
}
