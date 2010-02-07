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

/*@ predicate disjoint_strings{L}(char *s1, char *s2) =
     \forall integer i, j;
        0 <= i < strlen(s1) && 0 <= j < strlen(s2) ==> s1 + i != s2 + j;
*/

/*@ predicate disjoint_strings_len{L}(char *s1, char *s2, integer l) =
     \forall integer i, j;
        0 <= i <= l && 0 <= j <= strlen(s2) ==> s1 + i != s2 + j;
*/

/*@ predicate contains_string_at_i{L}(char *big, char *little, integer i) =
     \forall integer k; 0 <= k && k < strlen(little) && (k + i) < strlen(big) && big[k + i] == little[k];
*/

__BEGIN_DECLS
/*@ requires valid_string(s);
    requires valid_string(append);
    requires disjoint_strings(s, append);
    requires disjoint_strings_len(s, append, strlen(s) + strlen(append));
    requires \valid_range(s, 0, strlen(s) + strlen(append));
	assigns s[..];
    ensures strlen(s) == strlen{Old}(s) + strlen(append);
    ensures \forall integer i; 0 <= i < strlen{Old}(s) ==> s[i] == \old(s[i]);
    ensures \forall integer j; strlen{Old}(s) <= j < strlen(s) ==> s[j] == append[j - strlen{Old}(s)];
    ensures  \result == s;
 */
char	*strcat(char *s, const char *append);
/*@ requires valid_string(s);
    assigns \nothing;
    behavior b1:
       assumes c == '\0';
       ensures \result == \null;
    behavior b2:
       assumes strlen(s) == 0;
       ensures \result == \null;
    behavior b3:
		assumes c != '\0' && strlen(s) > 0;
        ensures \exists integer i; 0 <= i < strlen(s) && s[i] == c ==>
		   \forall integer j; 0 <= j < i && s[j] != c ==> \result == s+i;
	behavior b4:
		assumes c != '\0' && strlen(s) > 0;
		assumes \forall integer i; 0 <= i <= strlen(s) && s[i] != c;
	    ensures \result == \null;
 */
char	*strchr(const char *s, int c);
/*@  requires valid_string(s1);
     requires valid_string(s2);
     assigns \nothing;
     ensures (strlen(s1) == strlen(s2) && \forall integer i; 0 <= i <= strlen(s1) && s1[i] == s2[i]) ==> \result == 0;
     ensures \exists integer i; 0<=i<= strlen(s1) && 0<=i<= strlen(s2) && s1[i] <  s2[i]  &&
		  (\forall integer k; 0 <= k < i ==> s1[k] == s2[k])  ==> \result < 0;
     ensures \exists integer i; 0<=i<= strlen(s1) && 0<=i<= strlen(s2) && s2[i] >  s1[i] &&
		  (\forall integer k; 0 <= k < i ==> s1[k] == s2[k]) ==> \result > 0;
 */
int	 strcmp(const char *s1, const char *s2);
/*@ requires valid_string(from);
    requires disjoint_strings(to, from);
    requires disjoint_strings_len(to, from, strlen(from));
    requires \valid_range(to, 0, strlen(from));
    assigns to[0..];
    ensures \forall integer i; 0 <= i < strlen(from) ==> to[i] == from[i];
    ensures \result == to;
 */
char	*strcpy(char *to, const char *from);
/*@ requires valid_string(s);
    assigns \nothing;
    ensures \result == strlen(s);
 */
size_t	 strlen(const char *s);
/*@
  requires valid_string(src);
  requires valid_string(dst);
  requires \valid_range(dst, 0, strlen(dst) + n);
  requires \valid_range(dst, 0, strlen(dst) + strlen(src));
  requires disjoint_strings(src, dst);
  requires disjoint_strings_len(dst, src, strlen(dst) + strlen(src) + 1);
  requires disjoint_strings_len(dst, src, strlen(dst) + n + 1);
  ensures \result == dst;
  behavior b1:
	  assumes n == 0;
	  assigns \nothing;
  behavior b2:
      assumes n > 0 && strlen(src) <= n - 1;
      assigns dst[..];
	  ensures strlen(dst) == strlen{Old}(dst) + strlen(src);
	  ensures \forall integer k; 0 <= k < strlen{Old}(dst) ==> dst[k] == \old(dst[k]);
	  ensures \forall integer k; 0 <= k < strlen(src) ==>
			dst[k + strlen{Old}(dst)] == src[k];
  behavior b3:
      assumes n > 0  && strlen(src) > n - 1;
      assigns dst[..];
	  ensures strlen(dst) == strlen{Old}(dst) + n;
	  ensures \forall integer k; 0 <= k < strlen{Old}(dst) ==> dst[k] == \old(dst[k]);
	  ensures \forall integer k; 0 <= k < n ==>
			dst[k + strlen{Old}(dst)] == src[k];
 */
char	*strncat(char *dst, const char *src, size_t n)
		__attribute__ ((__bounded__(__string__,1,3)));
/*@  requires valid_string(s1);
     requires valid_string(s2);
     requires n < INT_MAX;
     assigns \nothing;
     ensures n == 0 ==> \result == 0;
	 ensures (n > 0 ==> \forall integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && s1[i] == s2[i]) ==> \result == 0;
	 ensures \result < 0 ==> (n > 0 && \exists integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && s1[i] < s2[i] ==>
	 		(\forall integer k; 0 <= k < i ==> s1[k] == s2[k])) ;
	 ensures \result > 0 ==> (n > 0 && \exists integer i; 0 <= i <= minimum(n-1, minimum(strlen(s1), strlen(s2))) && s1[i] > s2[i] ==>
			(\forall integer k; 0 <= k < i ==> s1[k] == s2[k]));
 */
int	 strncmp(const char *s1, const char *s2, size_t n);

/*@ requires valid_string(src);
    requires \valid_range(dst, 0, n);
    requires disjoint_strings(dst, src);
    requires disjoint_strings_len(dst, src, n);
    ensures \result == dst;
    behavior b1:
		assumes n == 0;
		assigns \nothing;
	behavior b2:
		assumes n > 0 && strlen(src) >= n;
		assigns dst[..];
		ensures \forall integer i; 0 <= i < n ==> dst[i] == src[i];
	behavior b3:
		assumes n > 0 && strlen(src) < n;
		assigns dst[0..];
		ensures \forall integer i; 0 <= i < strlen(src) ==> dst[i] == src[i];
		ensures \forall integer i; strlen(src) <= i < n ==> dst[i] == 0;
 */
char	*strncpy(char *dst, const char *src, size_t n)
		__attribute__ ((__bounded__(__string__,1,3)));
/*@ requires valid_string(s);
    assigns \nothing;
    behavior b1:
       assumes c == '\0';
       ensures \result == \null;
    behavior b2:
       assumes strlen(s) == 0;
       ensures \result == \null;
    behavior b3:
		assumes c != '\0' && strlen(s) > 0;
        ensures \exists integer i; 0 <= i < strlen(s) && s[i] == c &&
         (\forall integer j; i < j < strlen(s) ==> s[j] != c) ==> \result == s+i;
    behavior b4:
		assumes c != '\0' && strlen(s) > 0;
		assumes \forall integer i; 0 <= i < strlen(s) && s[i] != c;
		ensures \result == \null;
 */
char	*strrchr(const char *s, int c);

/*@
  requires valid_string(s);
  requires valid_string(find);
  assigns \nothing;
  behavior b1:
    assumes strlen(find) == 0;
    ensures \result == s;
  behavior b2:
    assumes strlen(s) == 0;
    assumes strlen(find) > 0;
    ensures \result == \null;
  behavior b3:
    assumes strlen(s) >= strlen(find) > 0;
    assumes \exists integer i; 0 <= i <= (strlen(s) - strlen(find)) && contains_string_at_i(s, find, i) &&
               \forall integer j; 0 <= j < i ==> !contains_string_at_i(s, find, j);
    ensures contains_string_at_i(\result, find, 0);
  behavior b4:
    assumes \forall integer i; 0 <= i < strlen(s) && s[i] != *find;
    ensures \result == \null;
  behavior b5:
    assumes strlen(s) >= strlen(find) && strlen(find) > 0;
    ensures \forall integer i; 0 <= i < strlen(s) && !contains_string_at_i(s, find, i) ==> \result == \null;
 */
char	*strstr(const char *s, const char *find);

#if __BSD_VISIBLE
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
size_t	 strlcat(char *dst, const char *src, size_t siz)
		__attribute__ ((__bounded__(__string__,1,3)));
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
size_t	 strlcpy(char *dst, const char *src, size_t siz)
		__attribute__ ((__bounded__(__string__,1,3)));
#endif
__END_DECLS

#endif /* _STRING_H_ */
