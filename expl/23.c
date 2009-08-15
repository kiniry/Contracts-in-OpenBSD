// adding the assertions help prove preservation of the loop invariant. assert itself only proved by z3.

/*@ axiomatic Predicate_remove_copy {

        logic integer predicate_remove_copy{La,Lb}(int* a, int* b, integer i_a, integer i_b, int value);

        axiom predicate_remove_copy_empty{La,Lb}:
         \forall int* a, int* b, value, integer i_a, i_b;
         0 > i_a && 0 > i_b ==> predicate_remove_copy{La,Lb}(a, b, i_a, i_b, value) == 0;

        axiom predicate_remove_copy_equal_value{La,Lb}:
         \forall int* a, int* b, value, integer i_a, i_b;
         0 <= i_a && \at(a[i_a],La) == value ==>
         predicate_remove_copy{La,Lb}(a, b, i_a, i_b, value) ==
         predicate_remove_copy{La,Lb}(a, b, i_a-1, i_b, value);

         axiom predicate_remove_copy_not_equal_value{La,Lb}:
         \forall int* a, int* b, value, integer i_a, i_b;
         0 <= i_a && 0 <= i_b && (\at(a[i_a],La) != value <==> \at(a[i_a],La) == \at(b[i_b],Lb)) ==>
         predicate_remove_copy{La,Lb}(a, b, i_a, i_b, value) ==
         predicate_remove_copy{La,Lb}(a, b, i_a-1, i_b-1, value)+1;

         axiom predicate_remove_copy_label{La,Lb1,Lb2}:
         \forall int* a, int* b, value, integer i_a, i_b;
         (\forall integer i; 0<= i <= i_b ==>
            \at(b[i],Lb1) == \at(b[i],Lb2)) ==>
         predicate_remove_copy{La,Lb1}(a,b,i_a,i_b,value) ==
         predicate_remove_copy{La,Lb2}(a,b,i_a,i_b,value);

       }
    */
    /*@
     requires 0 <= length;
     requires \valid_range (a, 0, length-1);
     requires \valid_range (dest, 0, length-1);

    ensures 0 <= \result <= length;

    ensures \forall integer k; 0 <= k < \result ==> dest[k] != value;
    ensures \result == predicate_remove_copy{Old,Here}(a, dest, length-1, \result-1, value);


    */
int remove_copy_array (int* a, int length, int* dest, int value )
{
    int i_a = 0;
    int i_dest = 0;


    /*@
    loop invariant 0 <= i_a <= length;
    loop invariant i_dest <= i_a;
    loop invariant 0 <= i_dest <= length;

    loop invariant \forall integer k; 0 <= k < i_dest ==> dest[k] != value;
    loop invariant i_dest == predicate_remove_copy{Pre,Here}(a, dest, i_a-1, i_dest-1, value);
    */
    for ( ; i_a != length; ++i_a)

        if (a[i_a] != value)
        {
            dest[i_dest] = a[i_a];
            /*@assert
            i_dest+1==predicate_remove_copy{Pre,Here}(a,dest,i_a,i_dest,value);
            */

            ++i_dest;
        }


    return i_dest;

}

