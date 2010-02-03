/*	$OpenBSD: strlcpy.c,v 1.11 2006/05/05 15:27:38 millert Exp $	*/

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

// Proven by Z3 (-1 po in b2) +2 pli by simplify.

// param name siz different.

/*
 * Copy src to string dst of size siz.  At most siz-1 characters
 * will be copied.  Always NUL terminates (unless siz == 0).
 * Returns strlen(src); if retval >= siz, truncation occurred.
 */
/*@ requires \valid_range(dst, 0, siz);
    requires valid_string(src);
    requires disjoint_strings_len(dst, src, siz);
    requires disjoint_strings_len2(dst, src, siz);
    requires disjoint_strings_len(dst, src, strlen(src));
    requires disjoint_strings_len2(dst, src, strlen(dst));
    requires strlen(src) < INT_MAX;
	behavior b1:
		assumes siz >= 1;
		assumes siz <= strlen(src) + 1;
		assigns dst[..];
		ensures \forall integer i; 0 <= i < (siz - 1) ==> dst[i] == src[i];
		ensures dst[siz - 1] == 0;
		ensures \false;
		ensures \result == strlen(src);
	behavior b2:
		assumes siz > (strlen(src) + 1);
		assigns dst[..];
		ensures \forall integer i; 0 <= i <= strlen(src) ==> dst[i] == src[i];
		ensures \false;
		ensures \result == strlen(src);
	disjoint behaviors  b0, b1, b2;
 */
size_t
strlcpy(char *dst, const char *src, size_t siz)
{
	char *d = dst;
	const char *s = src;
	size_t n = siz;
	//@ assert src[strlen(src)]  == 0;
	/* Copy as many bytes as will fit */
	if (n != 0) {
		/*@
		   for b1, b2 : loop assigns n, d, s, dst[..];
		   for b1, b2: loop assigns n;
		   for b1, b2: loop variant n;
		   for b1, b2: loop invariant 0 < n <= siz;
		   for b2 : loop invariant 0 <= (s-src) <= strlen(src);
		   for b1 : loop invariant 0 <= (s-src) < siz <= strlen(src) + 1;
		   for b1, b2: loop invariant \base_addr(s) == \base_addr(src);
		   for b1, b2: loop invariant \base_addr(d) == \base_addr(dst);
		   for b1, b2: loop invariant \valid_range(dst, 0, siz);
		   for b1, b2: loop invariant \valid_range(src, 0, strlen(src));
		   for b1, b2: loop invariant (d-dst) == (s-src);
		   for b1, b2: loop invariant (siz - n) == (s-src);
		   for b1 : loop invariant \forall integer k; 0 <= k < (s-src) <= siz ==> dst[k] == src[k];
		   for b2 : loop invariant \forall integer k; 0 <= k < (s-src) ==> dst[k] == src[k];
		   for b1 : loop invariant \forall integer k; 0 <= k < (s-src) <= strlen(src) ==> src[k] != '\0';
		   for b2:  loop invariant \forall integer k; 0 <= k < (s-src) <= strlen(src) ==> src[k] != '\0';
		   for b1, b2: loop invariant \forall integer k; 0 <= k <= strlen(src) ==> src[k] == \at(src[k], Pre);
		 */
		while (--n != 0) {
			if ((*d++ = *s++) == '\0')
				break;
		}
		//@ assert siz > strlen(src) + 1 ==> s-src == strlen(src) + 1;
	}

	/* Not enough room in dst, add NUL and traverse rest of src */
	if (n == 0) {
		if (siz != 0)
			*d = '\0';		/* NUL-terminate dst */
		//@ assert (d-dst) == (siz - 1);
		//@ assert siz <= strlen(src) + 1;
		//@ ghost char *p = s;
		/*@
		 for b0, b1: loop assigns s;
		 for b0, b1: loop invariant \base_addr(s) == \base_addr(src);
		 for b0, b1: loop invariant \base_addr(s) == \base_addr(p);
		 for b0, b1: loop invariant \valid_range(src, 0, strlen(src));
		 for b0, b1: loop invariant p - src <= s - src <= strlen(src) + 1;
		 for b0, b1: loop invariant \forall integer k; p - src <= k < (s-src) <= strlen(src) ==> src[k] != '\0';
		 for b0, b1: loop invariant \forall integer k; 0 <= k <= strlen(src) ==> src[k] == \at(src[k], Pre);
		*/
		while (*s++)
			;
	}
	//@ assert *(s-1) == 0;
	//@ assert (s - src - 1) == strlen(src);
	return(s - src - 1);	/* count does not include NUL */
}
