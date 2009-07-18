// string length
// not finalized.
/*@
  @ inductive null_terminated {L}(char *s){
  @   case empty : \forall char *p; (\valid(p) && *p == '\0') => null_terminated(p);
  @   case non_empty : \forall char *p2; (\valid(p2) && \valid(p2 + 1) && null_terminated(p2 + 1)) ==> null_terminated (p2) ;
  @}
*/

/*@
requires \valid(s);
requires null_terminated(s); // @terminates null_terminated(s);
assigns \nothing;
ensures \result >= 0;
ensures s[\result] == '\0';

*/
 unsigned int strlen (const char *s)
 {
     unsigned int n = 0;
     //@ loop invariant 0<= n && \valid(s);
     while ( *s != '\0')
     {
    	 //@assert n < INT_MAX;
         n++;
         s++;
         //@assert \valid(s);
     }
     return n;
 }



