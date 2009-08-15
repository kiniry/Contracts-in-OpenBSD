/*@
     requires 0 <= length;
     requires \valid_range (a, 0, length-1);
     requires \valid_range (b, 0, length-1);

     ensures \result == length;
     ensures \forall integer k; 0 <= k < length ==>
     (a[k] == old_value ==>        b[k] == new_value);
     ensures \forall integer k; 0 <= k < length ==>
     (a[k] != old_value ==>        b[k] == a[k]);

    */
int replace_copy_array (int* a, int length, int* b, int old_value, int new_value )
{
    int i = 0;
    /*@
     loop invariant 0 <= i <= length;

     loop invariant \forall integer k; 0 <= k < i ==>
        (a[k] == old_value ==>
        b[k] == new_value);

    loop invariant \forall integer k; 0 <= k < i ==>
    (a[k] != old_value ==>
    b[k] == a[k]);

    */
    for (; i != length; ++i)
    {
        if (a[i]==old_value)
            b[i] = new_value;
        else
            b[i] = a[i];
    }
    return i;
}
