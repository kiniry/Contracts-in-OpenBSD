#define MAX 1000
#define N 4

int counters[N];

/*@ requires \forall int i; 0 <= i < N ==> counters[i] >= 0 &&
counters[i] < MAX;
    requires 0 < n && n <= N;
    assigns \nothing;
 */
int f(int n)
{
  int total = 0;
  int total_min_0;
  int i;

  /*@ loop invariant total >= 0;
      loop invariant 0 <= i && i <= n;
      loop invariant total <= i * MAX;
      loop invariant \forall integer j; 0<=j<i ==> total >= counters[j];
   */
  for (i = 0; i < n; i++) {
    total += counters[i];
  }

  /*@ assert total >= counters[0];
   */
  total_min_0 = total - counters[0];

  return total_min_0;
}

void main(void)
{
  counters[0] = 1;
  counters[1] = 0;
  counters[2] = 3;
  counters[3] = 4;
  f(N);
  return;
}
