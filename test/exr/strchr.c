// strchr - find chr in string.
// not finalized.

//#pragma JessieIntegerModel(modulo) //temp

/*@
   requires \valid(s);
   requires \exists int k; 0<=k<=INT_MAX && \valid_range(s, 0, k) && s[k] == '\0';
   terminates \exists int k; 0<=k<=INT_MAX && \valid_range(s, 0, k) && s[k] == '\0';
   assigns \nothing;
   behavior found:
       assumes \exists int k; 0 <= k <= INT_MAX && \valid(s+k) && s[k] == c;
	   ensures \valid(\result) && *\result== c;
   behavior not_found:
	   assumes \forall int k; 0 <= k <= INT_MAX && \valid(s+k) && s[k] != c;
       ensures \result == NULL;
   disjoint behaviors found, not_found;
 */
 char * strchr(const char *s, char c)
 {
	 /*@ loop invariant \valid(s);
	  * for not_found : loop invariant \at(*s, Pre) != c && \at(*s, Pre) != '\0';
	 */
	 while (s && *s != '\0' && *s != c) {
		 //@ invariant \at(*s, Here) != c && \at(*s, Here) != '\0';
		 s++;
	 }
	 if (s && *s == c)
		 return s;
	 return NULL;
 }
