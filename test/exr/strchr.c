// strchr - find chr in string.
// not finalized.

#pragma JessieIntegerModel(modulo) //temp

/*@
   requires sizeMax > 0 && sizeMax < INT_MAX;
   requires \valid_range(s, 0, sizeMax-1);
   requires \exists int k;0 <= k < sizeMax && s[k] == '\0'; // null_terminated.
   assigns \nothing;

   behavior found:
	   ensures \valid(\result) => *\result == c;
   behavior not_found:
       ensures \result == NULL => \forall int k; 0 <= k < sizeMax && \valid(s+k) && s[k] != c;
   disjoint behaviors found, not_found;
 */
 char * strchr(const char *s, unsigned int sizeMax, char c)
 {
	 unsigned int i = 0;
	 char *p = NULL;

	 /*@ loop invariant 0 <= i <= sizeMax;
	     loop invariant \valid(s);
	     loop invariant (p == NULL) || (\valid(p) && *p == c);
	 */
	 while (i < sizeMax && *s != '\0') {
		 if (c == *s)
		 {
			 p = s;
			 break;
		 }
		 i++;
		 s++;
	 }

	 return p;
 }
