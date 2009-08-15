/*@
 requires 0 < length;
*/
int loopinvariant(int length)
{
 int i = 0;
 /*@
     loop invariant 0 <= i < length;
 */
 while(++i != length)
 {}

 i = 0;
 i++;
 /*@
     loop invariant 0 <= i <= length;
 */
 while(i != length)
 {
 i++;
 }
 return 0;
}

