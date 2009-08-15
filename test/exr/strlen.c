// string length
// not finalized.

//#pragma JessieIntegerModel(modulo) //temp

/*@
requires \valid_string(s);
terminates \valid_string(s);
assigns \nothing;
ensures \result >= 0;
ensures s[\result] == '\0' && \forall int k; 0 <= k < \result && s[k] != '\0';
*/
 unsigned int strlen (const char *s)
 {
     unsigned int n = 0;
     char *p = s;
     /*@ loop invariant p >= s && n == (p-s);
         loop invariant \forall unsigned int k; 0 < k < n ==> s[k] != '\0';
         //loop invariant \forall unsigned int k; n <= k < strlen(s) ==> s[k] != \at(s[k], Pre);
       */
     while ( *p != '\0')
     {
    	 n++;
         p++;
     }
     //@ assert *p == '\0';
     return n;
 }



