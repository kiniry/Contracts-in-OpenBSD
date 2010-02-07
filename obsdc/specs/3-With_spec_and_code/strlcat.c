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

// Proven by Z3 (b0: 5/5, b1: 7/7, b2: 19/21, default: 142/143 (assertion), safety: 51/52 ==> legitimate but safe).
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
  requires valid_string(src);
  requires valid_string(dst);
  requires \valid_range(dst, 0, siz);
  requires disjoint_strings(dst, src);
  requires disjoint_strings_len(dst, src, siz);
  ensures \forall integer k; 0 <= k < strlen{Old}(dst) ==> dst[k] == \old(dst[k]);
  ensures \result == strlen(src) + minimum(strlen{Old}(dst), siz);
  behavior b0:
	  assumes siz == 0 || strlen(dst) >= siz;
	  assigns \nothing;
  behavior b1:
      assumes siz > 0 && strlen(dst) < siz;
      assumes 1 == (siz - strlen(dst));
      assigns dst[..];
	  ensures strlen(dst) == strlen{Old}(dst);
  behavior b2:
      assumes siz > 0 && strlen(dst) < siz;
      assumes 1 < (siz - strlen(dst));
      assigns dst[..];
	  ensures strlen(src) < (siz - strlen{Old}(dst) - 1) ==> (\forall integer k; 0 <= k < strlen(src) ==> dst[k + strlen{Old}(dst)] == src[k]);
	  ensures strlen(src) >= (siz - strlen{Old}(dst) - 1) ==> (\forall integer k; 0 <= k < (siz - strlen{Old}(dst) - 1) ==> dst[k + strlen{Old}(dst)] == src[k]);
	  ensures strlen(src) < (siz - strlen{Old}(dst) - 1) ==> strlen(dst) == strlen{Old}(dst) + strlen(src);
	  ensures strlen(src) >= (siz - strlen{Old}(dst) - 1) ==> strlen(dst) == siz - 1;
 */
size_t
strlcat(char *dst, const char *src, size_t siz)
{
	char *d = dst;
	const char *s = src;
	size_t n = siz;
	size_t dlen;

	/* Find the end of dst and adjust bytes left but don't go past end */
	/*@
	    loop assigns n, d;
	    loop invariant 0 <= n <= siz;
	    loop invariant \base_addr(d) == \base_addr(dst);
	    loop invariant \valid(d);
	    loop invariant 0 <= (d - dst) <= strlen{Pre}(dst);
	    loop invariant d - dst == siz - n;
	    loop invariant \forall integer k; 0 <= k < (d-dst) ==> dst[k] != '\0';
	 */
	while (n-- != 0 && *d != '\0')
		 d++;
	//@ assert siz < strlen{Pre}(dst) ==> (d-dst) == siz;
	//@ assert siz >= strlen{Pre}(dst) ==> (d-dst) == strlen{Pre}(dst);
	dlen = d - dst;
	//@ assert dlen <= siz;
	n = siz - dlen;
	if (n == 0)
		return(dlen + strlen(s));
	//@ assert n > 0;
	//@ assert siz > strlen{Pre}(dst);
	//@ assert (d-dst) == strlen{Pre}(dst);
	//@ assert n == (siz - strlen{Pre}(dst));

	//@ ghost char *p = d;
	//@ assert p-dst == strlen{Pre}(dst);
	//@ assert \forall integer k; 0 <= k < (d-p) ==> dst[k] == \at(dst[k], Pre);
	/*@
	  @ loop assigns n, s, d, dst[p-dst..];
	    loop invariant 1 <= n <= (siz - strlen{Pre}(dst));
	    loop invariant \base_addr(d) == \base_addr(dst);
	    loop invariant \base_addr(s) == \base_addr(src);
	    loop invariant 0 <= (s-src) <= strlen(src);
	    loop invariant \valid(s);
	    loop invariant \valid(d);
	    loop invariant n > 1 ==> d-p == s-src;
	    loop invariant (siz - strlen{Pre}(dst)) - n == d - p;
	    loop invariant \forall integer k; 0 <= k < (s-src) ==> src[k] != 0;
	    loop invariant \forall integer k; 0 <= k <= strlen(src) ==> src[k] == \at(src[k], Pre);
	    loop invariant \forall integer k; 0 <= k < (p-dst) ==> dst[k] == \at(dst[k], Pre);
	    loop invariant \forall integer k; 0 <= k < strlen{Pre}(dst) ==> dst[k] == \at(dst[k], Pre);
	    loop invariant \forall integer k; 0 <= k < (d-p) <= strlen(src)  ==> dst[k + strlen{Pre}(dst)] == src[k];
	 */
	while (*s != '\0') {
		if (n != 1) {
			*d++ = *s;
			n--;
		}
		s++;
	}
	*d = '\0';
	//@ assert dst[d-dst] == 0;
	//@ assert d-dst == strlen(dst);
	//@ assert s-src == strlen(src);
	return(dlen + (s - src));	/* count does not include NUL */
}
