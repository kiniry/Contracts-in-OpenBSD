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

// Proven by Simplify.

// param name siz different.

/*
 * Copy src to string dst of size siz.  At most siz-1 characters
 * will be copied.  Always NUL terminates (unless siz == 0).
 * Returns strlen(src); if retval >= siz, truncation occurred.
 */
/*@ requires \valid_range(dst, 0, siz);
    requires valid_string(src);
    ensures \result == strlen(src);
    behavior b1:
		assumes siz == 0;
		assigns \nothing;
	behavior b2:
		assumes siz > 0;
		assigns dst;
		ensures \forall integer i; 0 <= i < minimum(siz, strlen(src)) ==> dst[i] == \old(src[i]);
		ensures dst[minimum(siz, strlen(src))] == 0;
 */
size_t
strlcpy(char *dst, const char *src, size_t siz)
{
	char *d = dst;
	const char *s = src;
	size_t n = siz;

	//@ ghost int lenSrc = strlen(src);

	/* Copy as many bytes as will fit */
	if (n != 0) {
		//@ ghost int i = 0;
		/*@
		   loop assigns n, d, s;
		   loop invariant 0 <= n <= siz;
		   loop invariant 0 <= i <= minimum(siz, strlen(src));
		   loop invariant valid_string(s) && \valid(d);
		   loop invariant \forall integer k; 0 <= k < i ==> dst[k] == src[k];
		   loop invariant \forall integer k; 0 <= k < i ==> src[k] != '\0';
		 */
		while (--n != 0) {
			if ((*d++ = *s++) == '\0') //@ ghost i++;
				break;
		}
	}

	/* Not enough room in dst, add NUL and traverse rest of src */
	if (n == 0) {
		if (siz != 0)
			*d = '\0';		/* NUL-terminate dst */
		/*@
		 loop assigns s;
		 loop invariant valid_string(s);
		 loop invariant s - src <= strlen(src);
		 loop invariant *s != 0;
		*/
		while (*s++)
			;
	}
	//@ assert s-src == lenSrc;
	return(s - src - 1);	/* count does not include NUL */
}
