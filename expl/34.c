/*@
    predicate swapped {L1, L2}(int* a, int* b) =
        \at(*a, L1) == \at(*b, L2) &&
        \at(*b, L1) == \at(*a, L2);
*/
/*@
    requires \valid(a);
    requires \valid(b);
    assigns *a;
    assigns *b;

    ensures *a == \old(*b);
    ensures *b == \old(*a);
    ensures swapped{Here, Old}(a,b);
*/
void swap (int* a, int* b )
{
    int c = *a;
    *a = *b;
    *b = c;
}

/*@
 requires 0 <= length;
 requires \valid_range(a, 0, length-1);
 requires \valid_range(b, 0, length-1);


 ensures \forall integer i; 0 <= i < length ==> swapped {Here, Old}(a+i, b+i);

*/
int swap_ranges_array(int* a, int length, int* b)
{
 int i = 0;
 int tmp;
 /*@
  loop invariant 0 <= i <= length;

  loop invariant \forall integer k;
   0 <= k < i ==> swapped {Here, Pre}(a+k, b+k);
  loop invariant \forall integer k;
   i <= k < length ==>
   \at(a[k], Here) == \at(a[k], Pre)&&
   \at(b[k], Here) == \at(b[k], Pre);
 */
  for (;i != length; i++)
  {
    swap(a+i, b+i);
  }
  return i;
}
