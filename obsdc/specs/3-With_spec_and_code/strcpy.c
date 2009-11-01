/*	$OpenBSD: strcpy.c,v 1.8 2005/08/08 08:05:37 espie Exp $	*/

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
__warn_references(strcpy,
    "warning: strcpy() is almost always misused, please use strlcpy()");
#endif

// Params don't match man.

/*@ requires \valid(to) && valid_string(from);
    assigns to;
    ensures \forall integer i; 0 <= i <= strlen(from) && to[i] == from[i];
    ensures \result == to;
 */
char *
strcpy(char *to, const char *from)
{
	char *save = to;

	//@ ghost char *origFrom = from;
	//@ ghost int lenFrom = strlen(from);
	/*@ loop assigns to, from;
	    loop invariant from >= origFrom && ((from-origFrom) <= lenFrom);
	    loop invariant (to-save) == (from - origFrom);
		loop invariant \valid(to) && valid_string(from);
		loop invariant \forall integer k; 0 <= k < (to-save) ==> save[k] == origFrom[k];
	*/
	for (; (*to = *from) != '\0'; ++from, ++to);
	return(save);
}
