// the following pragma allows to ignore potential arithmetic overflow

#pragma JessieIntegerModel(exact)

/* the \prod ACSL construct is not yet supported by the Jessie plugin
 * the following inductive definition is a work-around
 */

// is_prod(a,b,n) true whenever n = prod_{i=a..b} i

/*@ inductive is_prod(integer a, integer b, integer n) {
  @   case is_prod_empty :
  @      \forall integer a,b; a > b ==> is_prod(a,b,1);
  @   case is_prod_left :
  @      \forall integer a,b,n; a <= b && is_prod(a,b-1,n)
  @           ==> is_prod(a,b,b*n);
  @ }
  @*/

/*@ requires n >= 0;
  @ ensures is_prod(1,n,\result);
  //@ decreases n; // not yet supported by Jessie plugin
  @*/
int fact(int n) {
if (n == 0) return 1;
// simulating the VC for the decreases clause
//@ assert 0 <= n && n-1 < n;
return n * fact(n-1);
}
