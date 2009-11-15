/*	$OpenBSD: strlcat.c,v 1.13 2005/08/08 08:05:37 espie Exp $	*/

/*
 * Copyright (c) 1998 Todd C. Miller <Todd.Miller@courtesan.com>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

#include <sys/types.h>
#include <string.h>

// Proven by Simplify.
// Param siz diff.

// ??? not if siz == 0;
//from man: guarantee to NUL-terminate the result (as long as size is
//     larger than 0 or, in the case of strlcat(), as long as there is at least
//     one byte free in dst)

// ??? only in normal cond.
/* from man: The strlcpy() and strlcat() functions return the total length of the
     string they tried to create.  For strlcpy() that means the length of src.
     For strlcat() that means the initial length of dst plus the length of
     src.  While this may seem somewhat confusing, it was done to make trunca-
     tion detection simple.
*/

/*
 * Appends src to string dst of size siz (unlike strncat, siz is the
 * full size of dst, not space left).  At most siz-1 characters
 * will be copied.  Always NUL terminates (unless siz <= strlen(dst)).
 * Returns strlen(src) + MIN(siz, strlen(initial dst)).
 * If retval >= siz, truncation occurred.
 */
/*@
  requires valid_string(src) && valid_string(dst) && \valid_range(dst, 0, siz);
  assigns dst;
  ensures \result == strlen(src) + minimum(siz, strlen(\old(dst)));
  behavior b1:
	  assumes siz == 0;
	  assigns \nothing;
  behavior b2:
      assumes siz > 0 && strlen(dst) < siz;
	  ensures strlen(dst) == \old(strlen(dst)) + minimum(siz, strlen(src));
	  ensures \forall integer k; 0 <= k < \old(strlen(dst)) ==> dst[k] == \old(dst[k]);
	  ensures \forall integer k; 0 <= k < minimum(siz, strlen(src)) ==>
			dst[k + \old(strlen(dst))] == src[k];
	  ensures dst[strlen(dst)] == '\0';
  behavior b3:
      assumes siz > 0 && strlen(dst) >= siz;
	  assigns \nothing;
 */
size_t
strlcat(char *dst, const char *src, size_t siz)
{
	char *d = dst;
	const char *s = src;
	size_t n = siz;
	size_t dlen;
	//@ ghost int lenSrc = strlen(src);
	//@ ghost int lenDst = strlen(dst);

	/* Find the end of dst and adjust bytes left but don't go past end */
	/*@
	  loop assigns n, d;
	  loop invariant 0 <= n <= siz;
	  loop invariant *d != '\0';
	  loop invariant d - dst <= lenDst;
	 */
	while (n-- != 0 && *d != '\0')
		d++;
	dlen = d - dst;
	n = siz - dlen;

	if (n == 0)
		return(dlen + strlen(s));
	//@ ghost int i = dlen;
	/*@
	  loop assigns n;
	  loop invariant *s != '\0';
	  loop invariant dlen <= i <= lenSrc;
	  loop invariant \forall integer k; 0 <= k < i ==> dst[k] == s[k - dlen];
	 */
	while (*s != '\0') {
		if (n != 1) {
			*d++ = *s;
			n--;
		}
		s++; //@ ghost i++;
	}
	*d = '\0';

	return(dlen + (s - src));	/* count does not include NUL */
}
