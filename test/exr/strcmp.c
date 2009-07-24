// string cmp: true/false

#include "string_util.h"
#include "strings.h"

/*@ requires valid_string(s1) && valid_string(s2);
    assigns \nothing;
    behavior equal:
      assumes strlen(s1) == strlen(s2) && \forall unsigned int i; 0 <= i <= strlen(s1) && s1[i] == s2[i];
      ensures \result == 1;
    behavior not_equal1:
      assumes strlen(s1) != strlen(s2);
      ensures \result == 0;
    behavior not_equal2:
      assumes strlen(s1) == strlen(s2) && \exists unsigned int i; 0<= i <= strlen(s1)&& s1[i] != s2[i];
      ensures \result == 0;
*/

int (strcmp)(const char *s1, const char *s2)
 {
	//@assert \valid(s1) && \valid(s2);

	unsigned int length1 = strlen(s1);
	unsigned int length2 = strlen(s2);
	unsigned int n = 0;
	/*@
	    loop invariant 0 <= n <= length1 && 0 <= n <= length2;
	    loop invariant \forall unsigned int k; 0 <= k < n && s1[k] == s2[k];
	    loop invariant \forall unsigned int k; 0 <= k < n && s1[n] != s2[n] ==> s1[k] == s2[k];
	*/
     while (n < length1 && n < length2 && s1[n] == s2[n]) {
        n++;
     }
     return ((s1[n] == s2[n]) ? 1 : 0);
 }
