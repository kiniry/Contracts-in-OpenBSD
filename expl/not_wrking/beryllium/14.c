//@ predicate is_positive ( integer x) = x > 0;

/*@ logic integer sign ( real x) =
 @ x > 0.0 ? 1 : ( x < 0.0 ? -1 : 0);
 @*/

// a complete verification of an ACSL specification has to provide a proof for each
// lemma.
//@ lemma mean_property : \forall integer x,y; x <= (x+y )/2 <= y;

/*@ inductive is_gcd ( integer a, integer b, integer d) {
@ case gcd_zero :
@ \forall integer n; is_gcd (n ,0, n);
@ case gcd_succ :
@ \forall integer a,b,d; is_gcd (b, a % b, d) ==> is_gcd (a,b,d);
@ }
@*/

/*@ axiomatic sign {
 @ logic integer sign ( realx);
 @ axiom sign_pos : \forall real x; x >= 0 ==> sign (x) == 1;
 @ axiom sign_neg : \forall real x; x <= 0 ==> sign (x) == -1;
 @ }
 @*/


// not working!
// /*@ logic integer max_index {L}( int t[], integer n) =
// @ (n ==0) ? 0 :
// @ (t[n -1]==0) ? n : max_index (t, n -1);
// @*/


/*@ axiomatic NbOcc {
  @ // nb_occ (t,i,j,e) gives the number of occurrences of e in t[i..j]
 @ // (in a given memory state labelled L)
 @ logic integer nb_occ {L}( double t[], integer i, integer j,
 @ double e);
 @ axiom nb_occ_empty {L}:
 @ \forall double t[], e, integer i, j;
 @ i > j ==> nb_occ (t,i,j,e) == 0;
 @ axiom nb_occ_true {L}:
 @ \forall double t[], e, integer i, j;
 @ i <= j && t[j] == e ==>
 @ nb_occ (t,i,j,e) == nb_occ (t,i,j -1,e) + 1;
 @ axiom nb_occ_false {L}:
 @ \forall double t[], e, integer i, j;
 @ i <= j && t[j] != e ==>
 @ nb_occ (t,i,j,e) == nb_occ (t,i,j -1,e);
 @ }
 @*/

