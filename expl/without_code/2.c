/*@ predicate is_permutation{S1,S2}(int *a, int *b, int s) =
@   \forall integer k;
@     0 <= k < s ==> \at(a[k],S1) == \at(a[k],S2);
@*/

/*@ ensures is_permutation{Here,Old}(a,a,s);
@ */
void permut(int *a, int s);
