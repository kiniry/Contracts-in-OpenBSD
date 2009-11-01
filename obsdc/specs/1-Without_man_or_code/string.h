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
/*@ requires valid_string(s1) && valid_string(s2);
    assigns \nothing;
    ensures \result == \null;
    behavior normal:
       assumes \valid_range(s1, 0, strlen(s1) + strlen(s2));
       assigns s1;
       ensures \forall integer i; 0 <= i < \at(strlen(s1), Old) && s1[i] == \old(s1[i]) && \result == s1 &&
               \forall integer j; \old(strlen(s1)) <= j < strlen(s1) && s1[j] == s2[j];
 */
char	*strcat(char *s1, const char *s2);
/*@ requires valid_string(s);
    assigns \nothing;
    ensures \exists integer i; 0 <= i < strlen(s) && s[i] == c ==> \result == s+i;
    ensures \forall integer i; 0 <= i < strlen(s) && s[i] != c ==> \result == \null;
 */
char	*strchr(const char *s, int c);
/*@ requires valid_string(s1) && valid_string(s2);
    assigns \nothing;
    behavior same_strings:
      assumes strlen(s1) == strlen(s2) && \forall integer i; 0 <= i < strlen(s1) && s1[i] == s2[i];
      ensures \result == 0;
    behavior s1_smaller:
      assumes strlen(s1) < strlen(s2) || (strlen(s1) == strlen(s2) && \exists integer i; 0<=i<strlen(s1) && s1[i] < s2[i]);
      ensures \result == -1;
    behavior s2_smaller:
      assumes strlen(s2) < strlen(s1) || (strlen(s1) == strlen(s2) && \exists integer i; 0<=i<strlen(s2) && s2[i] < s1[i]);
      ensures \result == 1;
 */
int	 strcmp(const char *s1, const char *s2);
/*@ requires valid_string(s1) && valid_string(s2);
    assigns s1;
    behavior normal:
       assumes strlen(s1) >= strlen(s2);
       ensures \forall integer i; 0 <= i < strlen(s2) && s1[i] == s2[i] && \result == s1;
    behavior error:
       assumes strlen(s1) < strlen(s2);
       assigns \nothing;
       ensures \result == \null;
 */
char	*strcpy(char *s1, const char *s2);
// not clear what this does.
size_t	 strcspn(const char *, const char *);
/*@ requires valid_string(s);
  @ assigns \nothing;
  @ ensures \result == strlen(s) && \forall unsigned int k; 0 <= k < \result && s[k] != '\0';
  @*/
size_t	 strlen(const char *s);
/*@
  requires \valid_range(s1, 0, minimum(n, strlen(s2)) -1) && valid_string(s2);
  assigns s1[0..minimum(n, strlen(s2)) - 1];
  ensures strlen(s1) == \old(strlen(s1)) + minimum(n, strlen(s2));
  ensures \forall integer k; 0 <= k < \old(strlen(s1)) ==> s1[k] == \old(s1[k]);
  ensures \forall integer k; \old(strlen(s1)) <= k < minimum(n, strlen(s2)) ==>
    s1[k] == s2[k-\old(strlen(s1))];
  ensures \result == s1;
 */
char	*strncat(char *s1, const char *s2, size_t n)
		__attribute__ ((__bounded__(__string__,1,3)));
/*@ requires valid_string(s1) && valid_string(s2);
    requires len <= strlen(s1) && len <= strlen(s2);
    assigns \nothing;
    behavior same_strings:
      assumes \forall integer i; 0 <= i < len  && s1[i] == s2[i];
      ensures \result == 0;
    behavior s1_smaller:
      assumes \exists integer i; 0 <=i< len && s1[i] < s2[i];
      ensures \result == -1;
    behavior s2_smaller:
      assumes \exists integer i; 0<=i< len && s2[i] < s1[i];
      ensures \result == 1;
 */
int	 strncmp(const char *s1, const char *s2, size_t len);
/*@ requires valid_string(s1) && valid_string(s2);
    assigns s1;
    behavior normal:
       assumes strlen(s1) >= minimum(strlen(s2), n);
       ensures \forall integer i; 0 <= i < minimum(strlen(s2), n) && s1[i] == s2[i] && \result == s1;
    behavior error:
       assumes strlen(s1) < minimum(strlen(s2), n);
       assigns \nothing;
       ensures \result == \null;
 */
char	*strncpy(char *s1, const char *s2, size_t n)
		__attribute__ ((__bounded__(__string__,1,3)));
// not clear what this does.
char	*strpbrk(const char *, const char *);
/*@
  @ requires valid_string(s);
  @ assigns \nothing;
  @ ensures \exists integer i; 0 <= i <= strlen(s) && s[i] == n &&
  @    (\forall integer j; i < j <= strlen(s) ==> s[j] != n) ==> \result == s+i;
  @ ensures \forall integer i; 0 <= i <= strlen(s) && s[i] != n ==> \result == \null;
 */
char	*strrchr(const char *s, int n);
/*@
  @ requires valid_string(s1) && valid_string(s2);
  @ assigns \nothing;
  @ ensures strlen(s1) < strlen(s2) ==> \result == \null;
  @ ensures strlen(s1) >= strlen(s2) && \exists integer i; 0 <= i <= (strlen(s1) - strlen(s2)) &&
  @   \forall integer k; i <= k <= strlen(s2) && s1[k] == s2[k] ==> \result == s1 + i;
  @ ensures strlen(s1) >=  strlen(s2) && \forall integer i; 0 <= i <= (strlen(s1) - strlen(s2)) &&
  @   \exists integer k; i <= k <= strlen(s2) && s1[k] != s2[k] ==> \result == \null;
 */
char	*strstr(const char *s1, const char *s2);

#if __BSD_VISIBLE
size_t	 strlcat(char *, const char *, size_t)
		__attribute__ ((__bounded__(__string__,1,3)));
size_t	 strlcpy(char *, const char *, size_t)
		__attribute__ ((__bounded__(__string__,1,3)));
#endif
__END_DECLS
#endif /* _STRING_H_ */
