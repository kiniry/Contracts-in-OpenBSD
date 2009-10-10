// loop assigns not working yet, will work for beryllium.

/*@
 requires 0 < n;
 requires \valid_range(a, 0, n-1);
 assigns  a[0..n - 1];
 ensures  \forall integer i; 0 <= i < n ==> a[i] == 0;
*/
void array_zero(int* a, int n)
{

    /*@
   loop invariant 0 <= i <= n;
   loop invariant \forall integer k; 0 <= k < i ==> a[k] == 0;
   loop assigns i, a[0..i-1];
    */
    for (int i = 0; i < n; i++)
    {
        a[i] = 0;
    }
}
