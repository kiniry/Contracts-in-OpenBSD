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

// X Z3 proves all but b5 1 0f 3 posts.

// man params don't match.
// note why?

// not done yet: 'first' occurence.

/*
 * Find the first occurrence of find in s.
 */
/*@ predicate contains_string_at_i{L}(char *big, char *little, integer i) =
  @   \forall integer k; 0 <= k && k < strlen(little) && (k + i) < strlen(big) && big[k + i] == little[k];
  @*/

/*@
  @ requires valid_string(s) && valid_string(find);
  @ assigns \nothing;
  @ behavior b1:
  @   assumes strlen(find) == 0;
  @   ensures \result == s;
  @ behavior b2:
  @   assumes strlen(s) < strlen(find);
  @   ensures \result == \null;
  @ behavior b3:
  @   assumes strlen(s) >= strlen(find);
  @   assumes \exists integer i; 0 <= i <= (strlen(s) - strlen(find)) && contains_string_at_i(s, find, i);
  @   ensures contains_string_at_i(\result, find, 0);
  @ behavior b4:
  @   assumes \forall integer i; 0 <= i < strlen(s) && s[i] != *find;
  @   ensures \result == \null;
  @ behavior b5:
  @   assumes !(\exists integer i; 0 <= i < strlen(s) && contains_string_at_i(s, find, i));
  @   ensures \result == \null;
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
		//@ ghost int lenS = strlen(s);
		//@ ghost int ind = 0;
		/*@
		  @ loop assigns s;
		  @ loop invariant s >= orig;
		  @ loop invariant 0 <= ind <= lenS;
		  @ loop invariant \forall integer k; 0 <= k < ind ==> !contains_string_at_i(orig, origFind, k);
		 */
		do {
			//@ ghost char *p = s;
			/*@ loop assigns s;
			  @ loop invariant sc != c && *s != '\0';
			  @ loop invariant 0 <= ind <= lenS;
			  @ loop invariant \forall integer j; 0 <= j < (s-p) ==> p[j] != *origFind;
			  @ loop invariant \forall integer j; 0 <= j < (s-p) ==> p[j] != 0;
			  @ loop invariant \forall integer k; 0 <= k < ind ==> !contains_string_at_i(orig, origFind, k);
			*/
			do {
				if ((sc = *s++) == 0) //ghost ind++;
					/*@ assert \forall integer k; 0 <= k <= lenS && !contains_string_at_i(orig, origFind, k); */ return (NULL);
			} while (sc != c);
		} while (strncmp(s, find, len) != 0);
		s--; //why?
		//@ assert contains_string_at_i(s, origFind, 0);
		//@ assert contains_string_at_i(orig, origFind, s-orig);
	}
	return ((char *)s);
}
