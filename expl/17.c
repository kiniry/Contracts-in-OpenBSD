// this is just to demonstrate use of ghost variables.

/*@
 requires 0 < n;
 requires \valid_range(a, 0, n-1);
 ensures  \forall int i; 0 <= i < n ==> a[i] == 0;
*/
void array_zero(int* a, int n){
  //@ ghost int *g = a;
 /*@ loop invariant 0 <= i <= n && \forall int k; 0 <= k < i ==> a[k] == 0;
     loop invariant g - a ==  i;
 */
 for(int i = 0;i< n;i++){
  a[i]=0;
  //@ ghost g++;
 }
}
