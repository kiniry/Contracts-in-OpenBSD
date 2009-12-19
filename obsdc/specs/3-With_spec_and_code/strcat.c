/*	$OpenBSD: strcat.c,v 1.8 2005/08/08 08:05:37 espie Exp $	*/

/*
 * Copyright (c) 1988 Regents of the University of California.
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

#if defined(APIWARN)
__warn_references(strcat,
    "warning: strcat() is almost always misused, please use strlcat()");
#endif

// Proven by Simplify

// man is confusing as it mixes N version.

/*@
	requires valid_string(s);
	requires valid_string(append);
	requires disjoint_strings_len(s, append, strlen(append));
	requires \valid_range(s, 0, strlen(s) + strlen(append));
	assigns s[..];
	ensures strlen(s) == strlen{Old}(s) + strlen(append);
	ensures \forall integer i; 0 <= i < strlen{Old}(s) ==> s[i] == \old(s[i]);
	ensures \forall integer j; strlen{Old}(s) <= j < strlen(s) ==> s[j] == append[j-strlen{Old}(s)];
	ensures  \result == s;
 */
char *
strcat(char *s, const char *append)
{
	char *save = s;
	/*@ loop assigns s;
		loop invariant 0 <= (s-save) <= strlen(save);
		loop invariant \valid(s);
		loop invariant \base_addr(s) == \base_addr(save);
		loop invariant \forall integer k; 0 <= k < (s-save) ==> save[k] != 0;
	*/

	for (; *s; ++s);

	//@ assert *s == '\0' && s == save + strlen(save);
	//@ assert \valid_range(s, 0, strlen(append));

	//@ ghost char *s_cat = s;
	//@ ghost char *origAppend = append;

	/*@ loop assigns s;
			loop invariant 0 <= (s-save) <= strlen(save);
			loop invariant \valid(s);
			loop invariant \base_addr(s) == \base_addr(save);
			loop invariant \forall integer k; 0 <= k < (s-save) ==> save[k] != 0;
		*/
		for (; *s; ++s);
		//@ assert *s == '\0' && s == save + strlen(save);
		//@ assert \valid_range(s, 0, strlen(append));

		//@ ghost char *s_cat = s;
		//@ ghost char *origAppend = append;

		/*@ loop assigns s, save[s_cat-save..], append;
			loop invariant \base_addr(s) == \base_addr(s_cat);
			loop invariant \base_addr(append) == \base_addr(origAppend);
			loop invariant \valid_range(origAppend, 0, strlen{Pre}(append));
			loop invariant \valid_range(s_cat, 0, strlen{Pre}(append));
			loop invariant (append-origAppend) == (s - s_cat);
			loop invariant 0 <= (append-origAppend) <= (strlen(origAppend));
			loop invariant \forall integer k; 0 <= k < (append-origAppend)  ==> origAppend[k] != 0;
			loop invariant \forall integer k; 0 <= k < (append-origAppend) ==> save[k + (s_cat-save)] == origAppend[k];
			loop invariant \forall integer k; 0 <= k < (append-origAppend)  ==> save[k + s_cat-save] != 0;
			loop invariant \forall integer k; 0 <= k < (s_cat-save) ==> save[k] == \at(s[k], Pre);
			loop invariant (append-origAppend) == (strlen(origAppend) + 1) ==> save[s_cat-save + append-origAppend - 1] == 0;
		*/
		while ((*s++ = *append++) != '\0');

	//@ assert s_cat[append-origAppend - 1] == 0;
	//@ assert strlen(s_cat) == append-origAppend -1;
	//@ assert strlen(origAppend) == append-origAppend -1;
	//@ assert strlen(s_cat) == strlen(origAppend);


	return(save);
}
