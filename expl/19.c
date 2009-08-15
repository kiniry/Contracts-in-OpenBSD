/*@ predicate pcond1(integer p) = (p>0)?\true:\false ;
 @ predicate pcond2(integer p) = (p<10)?\true:\false ;
 @*/

/*@
 //// ensures (pcond1(x) && pcond2(y)) ==> \result == 1 ;
 @ ensures \result == 1 <==> pcond1(x) && pcond2(y);
 @*/
int ftest1(int x, int y)
{
 return (x>0 && y<10);
}


/*@ predicate pcond3(integer p) = p > 0;
  @ predicate pcond4(integer p) = p < 10;
  @*/

/*@ behavior ok:
  @   assumes pcond3(x) && pcond4(y);
  @   ensures \result == 1;
  @ behavior ko:
  @   assumes !pcond3(x) || !pcond4(y);
  @   ensures \result == 0;
  @*/
int ftest2(int x, int y)
{
 return (x>0 && y<10);
}
