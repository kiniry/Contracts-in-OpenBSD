// string length
// not finalized.

//#pragma JessieIntegerModel(modulo) //temp

/*@
requires \valid(s);
requires \exists int k; 0<=k<=INT_MAX && \valid_range(s, 0, k) && s[k] == '\0';
terminates \exists int k; 0<=k<=INT_MAX && \valid_range(s, 0, k) && s[k] == '\0';
assigns \nothing;
ensures \result >= 0;
ensures \exists int k; 0<=k<=INT_MAX && \valid_range(s, 0, k) && s[k] == '\0' ==> \result == k;
*/
 unsigned int strlen (const char *s)
 {
     unsigned int n = 0;
     char *p = s;
     /*@ loop invariant 0<= n < INT_MAX && \valid(p);
         loop invariant \forall unsigned int k; 0 <= k && k < n && s[k] != '\0';
       */
     while ( *p != '\0')
     {
    	 //@assert n < INT_MAX;
         n++;
         p++;
     }
     //@ assert *p == '\0';
     return n;
 }



