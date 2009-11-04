// specs for top functions without looking at man or code - cleaned out rest of the functions out.
// had to add missing parameter names.
// had to create the include file structure and copy include files.

#ifndef _STRING_H_
#define	_STRING_H_

#include <sys/cdefs.h>
#include <machine/_types.h>

#ifndef	_SIZE_T_DEFINED_
#define	_SIZE_T_DEFINED_
typedef	__size_t	size_t;
#endif

#ifndef	NULL
#ifdef 	__GNUG__
#define	NULL	__null
#else
#define	NULL	0L
#endif
#endif

__BEGIN_DECLS
int	 memcmp(const void *, const void *, size_t);
/*@ requires valid_string(s) && valid_string(append) && \valid_range(s, 0, strlen(s) + strlen(append));
    assigns s;
    ensures strlen(s) == \old(strlen(s) + strlen(append));
    ensures \forall integer i; 0 <= i < \old(strlen(s)) ==> s[i] == \old(s[i]);
    ensures \forall integer j; \old(strlen(s)) <= j <= strlen(s) ==> s[j] == append[j];
    ensures  \result == s;
 */
char	*strcat(char *s, const char *append);
/*@ requires valid_string(s);
    assigns \nothing;
    ensures \exists integer i; 0 <= i < strlen(s) && s[i] == c ==>
       \forall integer j; 0 <= j < i && s[j] != c ==> \result == s+i;
    ensures \forall integer i; 0 <= i < strlen(s) && s[i] != c ==> \result == \null;
 */
char	*strchr(const char *s, int c);
/*@  requires valid_string(s1);
  @  requires valid_string(s2);
  @  assigns \nothing;
  @  ensures (strlen(s1) == strlen(s2) && \forall integer i; 0 <= i <= strlen(s1) && s1[i] == s2[i]) ==> \result == 0;
  @  ensures \exists integer i; 0<=i<= strlen(s1) && 0<=i<= strlen(s2) && (unsigned char)s1[i] < (unsigned char) s2[i] ==> \result < 0;
  @  ensures \exists integer i; 0<=i<= strlen(s1) && 0<=i<= strlen(s2) && (unsigned char) s2[i] > (unsigned char)s1[i] ==> \result > 0;
 */
int	 strcmp(const char *s1, const char *s2);
/*@ requires \valid(to) && valid_string(from);
    assigns to;
    ensures \forall integer i; 0 <= i <= strlen(from) && to[i] == from[i];
    ensures \result == to;
 */
char	*strcpy(char *to, const char *from);
/*@
  @ requires valid_string(s1) && valid_string(s2);
  @ assigns \nothing;
  @ ensures \exists integer i; 0 <= i < strlen(s1) &&
  @         \forall integer j; 0 <= j < strlen(s2) &&
  @          s2[j] != s1[i] ==> \result == i + 1;
 */
size_t strcspn(const char *s1, const char *s2);

/*@ requires valid_string(s);
  @ assigns \nothing;
  @ ensures \result == strlen(s) && \forall unsigned int k; 0 <= k < \result && s[k] != '\0';
  @*/
size_t	 strlen(const char *s);
/*@
  requires valid_string(src) && valid_string(dst) && \valid_range(dst, 0, strlen(dst) + minimum(n, strlen(src)));
  assigns dst;
  ensures \result == dst;
  behavior b1:
	  assumes n == 0 || strlen(src) == 0;
	  assigns \nothing;
  behavior b2:
      assumes n > 0 && strlen(src) > 0;
	  ensures strlen(dst) == \old(strlen(dst)) + minimum(n, strlen(src));
	  ensures \forall integer k; 0 <= k < \old(strlen(dst)) ==> dst[k] == \old(dst[k]);
	  ensures \forall integer k; 0 <= k < minimum(n, strlen(src)) ==>
			dst[k + \old(strlen(dst))] == src[k];
	  ensures dst[strlen(dst)] == '\0';
 */
char	*strncat(char *dst, const char *src, size_t n)
		__attribute__ ((__bounded__(__string__,1,3)));
/*@  requires valid_string(s1);
  @  requires valid_string(s2);
  @  assigns \nothing;
  @  ensures (n == 0) ==> \result == 0;
  @  ensures \forall integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && s1[i] == s2[i] ==> \result == 0;
  @  ensures \exists integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && (unsigned char)s1[i] < (unsigned char) s2[i] ==> \result < 0;
  @  ensures \exists integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && (unsigned char) s2[i] > (unsigned char)s1[i] ==> \result > 0;
 */
int	 strncmp(const char *s1, const char *s2, size_t n);
/*@ requires valid_string(dst) && valid_string(src);
    requires n < INT_MAX;
    requires \valid_range(dst, 0, minimum(n, strlen(src)));
    ensures \result == dst;
    behavior b1:
		assumes n == 0 || strlen(src) == 0;
		assigns \nothing;
	behavior b2:
		assumes n > 0 && strlen(src) > 0;
		assigns dst[0..n];
		ensures \forall integer i; 0 <= i < minimum(n, strlen(src)) ==> dst[i] == src[i];
	behavior b3:
		assumes n > 0 && strlen(src) > 0 && strlen(src) <= n;
		assigns dst[0..n];
		ensures \forall integer i; strlen(src) <= i <= n && dst[i] == '\0';
 */
char	*strncpy(char *dst, const char *src, size_t n)
		__attribute__ ((__bounded__(__string__,1,3)));
/*@
  @ requires valid_string(s1);
  @ assigns \nothing;
  @ ensures \exists integer i; 0 <= i < strlen(s2) &&
  @         \exists integer j; 0 <= j < strlen(s1) &&
  @          s2[i] == s1[j] ==> \result == s1+j;
  @ ensures \forall integer i; 0 <= i < strlen(s2) &&
  @         \forall integer j; 0 <= j < strlen(s1) &&
  @          s2[i] != s1[j] ==> \result == \null;
 */
char * strpbrk(const char *s1, const char *s2);
/*@
  @ requires valid_string(s);
  @ assigns \nothing;
  @ ensures \exists integer i; 0 <= i < strlen(s) && s[i] == c &&
  @    (\forall integer j; i < j < strlen(s) ==> s[j] != c) ==> \result == s+i;
  @ ensures (\forall integer i; 0 <= i < strlen(s) ==> s[i] != c) ==> \result == \null;
  @ ensures '\0' == c ==> \result == \null;
 */
char	*strrchr(const char *s, int c);
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
  @   assumes \exists integer i; 0 <= i <= (strlen(s) - strlen(find)) && contains_string_at_i(s, find, i) &&
                 \forall integer j; 0 <= j < i ==> !contains_string_at_i(s, find, j);
  @   ensures contains_string_at_i(\result, find, 0);
  @ behavior b4:
  @   assumes \forall integer i; 0 <= i < strlen(s) && s[i] != *find;
  @   ensures \result == \null;
  @ behavior b5:
  @   assumes strlen(s) >= strlen(find) && strlen(find) > 0;
  @   assumes \forall integer i; 0 <= i < strlen(s) && !contains_string_at_i(s, find, i);
  @   ensures \result == \null;
 */
char	*strstr(const char *s, const char *find);


#if __BSD_VISIBLE || __XPG_VISIBLE >= 420
int	 strcasecmp(const char *, const char *);
int	 strncasecmp(const char *, const char *, size_t);
char	*strdup(const char *);
#endif

#if __BSD_VISIBLE
size_t	 strlcat(char *, const char *, size_t)
		__attribute__ ((__bounded__(__string__,1,3)));
size_t	 strlcpy(char *, const char *, size_t)
		__attribute__ ((__bounded__(__string__,1,3)));
#endif
__END_DECLS

#endif /* _STRING_H_ */
