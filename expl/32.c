int t[100];

/*@ requires \forall integer k ; 0 <= k < 100 ==> t[k] == 1 ;
     ensures \forall integer k ; 0 <= k < 100 ==> t[k] == 2 ;
  */
void f(void)
{
   int i;

   /*@
        loop invariant (0 <= i <= 100) && (\forall integer k ; 0 <= k < i   ==> t[k] == 2)
        && (\forall integer k ; i <= k < 100 ==> t[k] == 1) ;
   */
   for (i=0; i<100; i++) t[i]++;
}

