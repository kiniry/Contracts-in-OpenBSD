#define true 1
#define false 0
typedef int bool;


/*@
 requires \valid(a+ (0..aLength-1));
 ensures \result == true  <==>  \exists int j; 0 <= j <= aLength-1 && a[j] == val;
*/
bool ContainsVal(int a[], int aLength, int val) {
 int i = 0;

 /*@ loop invariant \forall int j; 0 <= j <= i-1 ==> a[j] != val;
     loop invariant i >= 0;
 */
 while(i<aLength) {
     if(a[i] == val) return true;
     else i++;
 }
 return false;
}
