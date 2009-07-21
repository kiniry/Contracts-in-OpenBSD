// strchr - find chr in string.
// not finalized.

//#pragma JessieIntegerModel(modulo) //temp

/*@
   requires sizeMax > 0 && sizeMax < INT_MAX;
   requires \valid_range(s, 0, sizeMax-1);
   requires \exists int k;0 <= k < sizeMax && s[k] == '\0'; // null_terminated.
   assigns \nothing;

   behavior found:
       assumes \exists int k; 0 <= k < sizeMax && \valid(s+k) && s[k] == c;
	   ensures \valid(\result) && *\result== c;
   behavior not_found:
	   assumes \forall int k; 0 <= k < sizeMax && \valid(s+k) && s[k] != c;
       ensures \result == NULL;

   disjoint behaviors found, not_found;
 */
 char * strchr(const char *s, unsigned int sizeMax, char c)
 {
	 unsigned int i = 0;
	 char *p = NULL;
	 char *r = s;

	 /*@ loop invariant 0 <= i <= sizeMax;
	     loop invariant \valid(s) && \valid_range(s, 0, i);
	     loop invariant \forall unsigned int k; 0 <= k && k < i && (s[k] != '\0' && s[k] != c);
	     loop invariant i == s - p;
	 */
	 while (i < sizeMax && *r != '\0') {
		 if (c == *r)
		 {
			 p = r;
			 break;
		 }
		 i++;
		 //@assert (*r != '\0' && *r != c);
		 r++;
	 }
	 //@ assert (i == sizeMax || *r == '\0' || *r == c);
	 return p;
 }
