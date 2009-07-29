// separated clause not working.
/*@
requires 0 < n;
requires \separated(a+(..),b+(..));
requires \valid_range(a, 0, n-1) && \valid_range(b, 0, n-1);
ensures  \forall int k; 0 <= k < n ==> a[k] == b[k];
*/
void array_cpy(int* a, int n, int* b)
{
/*@ loop invariant 0 <= i <= n &&
     \forall int m; 0 <= m < i  ==> a[m] == b[m];
*/
for(int i = 0;i< n;i++){
  a[i]=b[i];
  }
}
