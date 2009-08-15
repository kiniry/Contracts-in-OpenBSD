/*@
     requires 0 <= length;
     requires \valid_range (a, 0, length-1);

     ensures \forall integer k;
         0 <= k < length ==>
         (\old(a[k]) == old_value ==>
       a[k]== new_value);
    */
void replace_array (int* a, int length, int old_value, int new_value )
{
    int i = 0;
    /*@
     loop invariant 0  <= i <= length;
     loop invariant \forall integer k;  0 <= k < i ==> (\at(a[k],Pre) == old_value ==> a[k] == new_value);
     loop invariant \forall integer k; i <= k < length ==> a[k] == \at(a[k],Pre);
    */
    for (; i != length; ++i)
    {
        if (a[i] == old_value)
        {
            a[i] = new_value;
        }
    }
}
