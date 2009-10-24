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
char	*strcat(char *, const char *);
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
/*@ requires valid_string(s);
  @ assigns \nothing;
  @ ensures \result == strlen(s) && \forall unsigned int k; 0 <= k < \result && s[k] != '\0';
  @*/
size_t	 strlen(const char *s);
char	*strncat(char *, const char *, size_t)
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
char	*strncpy(char *, const char *, size_t)
		__attribute__ ((__bounded__(__string__,1,3)));
char	*strrchr(const char *, int);
char	*strstr(const char *, const char *);


#if __BSD_VISIBLE || __XPG_VISIBLE >= 420
int	 strcasecmp(const char *, const char *);
int	 strncasecmp(const char *, const char *, size_t);
char	*strdup(const char *);
#endif


#endif /* _STRING_H_ */
