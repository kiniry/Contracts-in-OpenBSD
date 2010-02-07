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

// Proven by Z3 (b0 : 9/9, b1: 27/27 b2: 18/18 Default: 169/169 Safety: 71/71).

// param name siz different.

/*
 * Copy src to string dst of size siz.  At most siz-1 characters
 * will be copied.  Always NUL terminates (unless siz == 0).
 * Returns strlen(src); if retval >= siz, truncation occurred.
 */
/*@ requires \valid_range(dst, 0, siz);
    requires valid_string(src);
    requires disjoint_strings(dst, src);
    requires disjoint_strings_len(dst, src, siz);
    requires disjoint_strings_len(dst, src, strlen(src));
    requires strlen(src) < INT_MAX;
    ensures \result == strlen(src);
	behavior b0:
		assumes siz == 0;
		assigns \nothing;
	behavior b1:
		assumes siz >= 1;
		assumes siz <= strlen(src) + 1;
		assigns dst[..];
		ensures \forall integer i; 0 <= i < (siz - 1) ==> dst[i] == src[i];
		ensures dst[siz - 1] == 0;
	behavior b2:
		assumes siz > (strlen(src) + 1);
		assigns dst[..];
		ensures \forall integer i; 0 <= i <= strlen(src) ==> dst[i] == src[i];
 */
size_t
strlcpy(char *dst, const char *src, size_t siz)
{
	char *d = dst;
	const char *s = src;
	size_t n = siz;
	/* Copy as many bytes as will fit */
	if (n != 0) {
		/*@
		   loop assigns n, d, s, dst[..];
		   loop invariant 0 < n <= siz;
		   loop invariant siz > (strlen(src) + 1) ==> 0 <= (s-src) <= strlen(src);
		   loop invariant 1 <= siz <= strlen(src) + 1 ==> 0 <= (s-src) < siz <= strlen(src) + 1;
		   loop invariant \base_addr(s) == \base_addr(src);
		   loop invariant \base_addr(d) == \base_addr(dst);
		   loop invariant \valid(d);
		   loop invariant (s-src) <= strlen(src) ==> \valid(s);
		   loop invariant (d-dst) == (s-src);
		   loop invariant (siz - n) == (s-src);
		   loop invariant 1 <= siz <= strlen(src) + 1 ==> \forall integer k; 0 <= k < (s-src) <= siz ==> dst[k] == src[k];
		   loop invariant siz > (strlen(src) + 1) ==> \forall integer k; 0 <= k < (s-src) ==> dst[k] == src[k];
		   loop invariant \forall integer k; 0 <= k < (s-src) <= strlen(src) ==> src[k] != '\0';
		   loop invariant \forall integer k; 0 <= k <= strlen(src) ==> src[k] == \at(src[k], Pre);
		 */
		while (--n != 0) {
			if ((*d++ = *s++) == '\0')
				break;
		}
		//@ assert siz > strlen(src) + 1 ==> s-src == strlen(src) + 1;
		//@ assert siz > strlen(src) + 1 ==> n > 0;
	}

	/* Not enough room in dst, add NUL and traverse rest of src */
	if (n == 0) {
		if (siz != 0)
			*d = '\0';		/* NUL-terminate dst */
		//@ assert (d-dst) == (siz - 1);
		//@ assert siz <= strlen(src) + 1;
		//@ ghost char *p = s;
		/*@
		    loop assigns s;
			loop invariant \base_addr(s) == \base_addr(src);
			loop invariant \base_addr(s) == \base_addr(p);
			loop invariant (s-src) <= strlen(src) ==> \valid(s);
			loop invariant p - src <= s - src <= strlen(src);
			loop invariant \forall integer k; p - src <= k < (s-src) <= strlen(src) ==> src[k] != '\0';
			loop invariant \forall integer k; 0 <= k <= strlen(src) ==> src[k] == \at(src[k], Pre);
		*/
		while (*s++)
			;
	}
	//@ assert *(s-1) == 0;
	//@ assert (s - src - 1) == strlen(src);
	return(s - src - 1);	/* count does not include NUL */
}
