/*@ requires x >= 0;
 @ ensures \result >= 0;
 @ ensures \result * \result <= x;
 @ ensures x < ( \result + 1) * ( \result + 1);
 @*/
int isqrt(int x);

/*@ requires \valid(p);
    assigns *p;
    ensures *p == \old(*p) + 1;
 */
void incrstar(int *p);


/*@ // src and dest cannot overlap
 @ requires \base_addr ( src ) != \base_addr ( dest );
 @ // src is a valid C string
 @ requires \strlen ( src ) >= 0 ;
 @ // dest is large enough to store a copy of src up to the 0
 @ requires \valid_range (dest ,0, \strlen ( src ));
 @ ensures
 @ \forall integer k; 0 <= k <= \strlen ( src ) ==> dest [k] == src[k]
 @*/
 void strcpy ( char *dest , const char * src );
