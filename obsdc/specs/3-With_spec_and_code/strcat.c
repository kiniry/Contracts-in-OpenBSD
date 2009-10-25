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


// man not clear about appending a \0. Also, man is confusing as it mixes N version. e.g. copies none?

/*@ requires valid_string(s) && valid_string(append) && \valid_range(s, 0, strlen(s) + strlen(append));
    assigns s;
    ensures strlen(s) == \old(strlen(s) + strlen(append));
    ensures \forall integer i; 0 <= i < \at(strlen(s), Old) && s[i] == \old(s[i]);
    ensures \forall integer j; \old(strlen(s)) <= j < strlen(s) && s[j] == append[j];
    ensures  \result == s;
 */
char *
strcat(char *s, const char *append)
{
	char *save = s;

	//@ ghost int lenS = strlen(s);
	/*@ loop assigns s;
		loop invariant s >= save && ((s-save) <= lenS);
		loop invariant valid_string(s);
		loop invariant \forall integer k; 0 <= k < (s-save) ==> save[k] == \at(save[k], Pre);
	*/
	for (; *s; ++s);
	//@ assert *s == '\0' && s == save + lenS;

	//@ ghost char *s_cat = s;
	//@ ghost char *origAppend = append;
	//@ ghost int lenAppend = strlen(append);
	/*@ loop assigns s, append;
		loop invariant s >= s_cat && (s-s_cat) <= lenAppend;
		loop invariant append >= origAppend && (append-origAppend) <= lenAppend;
		loop invariant (append-origAppend) == (s - s_cat);
		loop invariant valid_string(s) && valid_string(append);
		loop invariant \valid_range(s, 0, lenAppend);
		loop invariant \forall integer k; 0 <= k < (s-s_cat) ==> s_cat[k] == origAppend[k];
	*/
	while ((*s++ = *append++) != '\0');
	return(save);
}
