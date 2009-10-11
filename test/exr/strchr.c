// strchr - find chr in string.
// use jessie_prolog for string utils.
#include "strings.h"


/*@ requires valid_string(s);
    assigns \nothing;
    behavior found:
      assumes \exists int i; 0 <= i <= strlen(s) && \valid(s + i) && s[i] == c;
      ensures *\result == c;
    behavior not_found:
      assumes \forall int i; 0 <= i <= strlen(s) && s[i] != c;
      ensures \result == NULL;

 */
 char * strchr(const char *s, char c)
 {
	 unsigned int length = strlen(s);
	 /*@
	     loop invariant 0 <= n <= length;
		 loop invariant \forall unsigned int k; 0 <= k < n && s[k] != c;
		 loop invariant \forall unsigned int k; 0 <= k < n  &&  s[n] == c ==> s[k] != c;
	 */
	 for (unsigned int n =0; n < length; n++) {
		 if (s[n] == c)
			 return s + n;
	 }

	  return NULL;
 }

