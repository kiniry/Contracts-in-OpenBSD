/*	$OpenBSD: strstr.c,v 1.5 2005/08/08 08:05:37 espie Exp $ */
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

// Proven by Z3 (b1: 3/3, b2: 3/3, b3: 3/3, b4: 3/3, b5: 3/3, default: 39/40 (assertion), safety: 12/13 ==> for strncmp pre-call).

// man params don't match.

/*
 * Find the first occurrence of find in s.
 */

/*@
  requires valid_string(s);
  requires valid_string(find);
  assigns \nothing;
  behavior b1:
    assumes strlen(find) == 0;
    ensures \result == s;
  behavior b2:
    assumes strlen(s) == 0;
    assumes strlen(find) > 0;
    ensures \result == \null;
  behavior b3:
    assumes strlen(s) >= strlen(find) > 0;
    assumes \exists integer i; 0 <= i <= (strlen(s) - strlen(find)) && contains_string_at_i(s, find, i) &&
               \forall integer j; 0 <= j < i ==> !contains_string_at_i(s, find, j);
    ensures contains_string_at_i(\result, find, 0);
  behavior b4:
    assumes \forall integer i; 0 <= i < strlen(s) && s[i] != *find;
    ensures \result == \null;
  behavior b5:
    assumes strlen(s) >= strlen(find) && strlen(find) > 0;
    ensures \forall integer i; 0 <= i < strlen(s) && !contains_string_at_i(s, find, i) ==> \result == \null;
 */
char *
strstr(const char *s, const char *find)
{
	char c, sc;
	size_t len;
	//@ ghost char *origFind = find;
	if ((c = *find++) != 0) {
		len = strlen(find);
		//@ ghost char *orig = s;
		/*@
		  loop invariant \base_addr(s) == \base_addr(orig);
		  loop invariant 0 <= s - orig <= strlen(orig);
		  loop invariant \forall integer k; 0 <= k < (s-orig) ==> orig[k] != 0;
		  loop invariant \forall integer k; 0 <= k < (s-orig) ==> !contains_string_at_i(orig, origFind, k);
		 */
		do {
			//@ ghost char *p = s;
			/*@ loop assigns s;
			    loop invariant \base_addr(s) == \base_addr(orig);
			    loop invariant \base_addr(s) == \base_addr(p);
		        loop invariant \valid_range(s, 0, strlen(s));
		        loop variant strlen(s);
		        loop invariant valid_string(orig);
			    loop invariant 0 <= s - orig <= strlen(orig);
			    loop invariant 0 <= s - p <= (strlen(orig) - (p-orig));
			    loop invariant \forall integer j; 0 <= j < (s-p) ==> orig[j + p - orig] != 0;
			    loop invariant \forall integer j; 0 <= j < (s-p) ==> orig[j + p - orig] != c;
			    loop invariant \forall integer k; 0 <= k < (s-orig) ==> orig[k] == \at(s[k], Pre);
			    loop invariant \forall integer k; 0 <= k < (s-orig) ==> origFind[k] == \at(find[k], Pre);
			*/
			do {
				if ((sc = *s++) == 0)
					return (NULL); /*@ assert \forall integer k; 0 <= k < strlen(orig) ==> !contains_string_at_i(orig, origFind, k); */
			} while (sc != c);
		} while (strncmp(s, find, len) != 0);
		s--;
		//@ assert *s == c;
		//@ assert contains_string_at_i(s, origFind, 0);
		//@ assert contains_string_at_i(orig, origFind, s-orig);
	}
	return ((char *)s);
}
