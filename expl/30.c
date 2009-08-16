#define MAX 5
int c[5];
int global;

void main(void)
{
  int i;

  /*@ loop invariant \forall integer j; 0 <= j < i ==> c[j] == 0;
      loop invariant 0 <= i && i <= MAX;
   */
  for (i = 0; i < MAX; i++)
    c[i] = 0;
  global = 0;

  //@ assert global == 0;
  //@ assert \forall integer i; 0 <= i < MAX ==> c[i] == 0;

  return;
}
