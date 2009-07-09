// __in_opt r, __in i
/*@ requires \valid(i);
  @ requires r == NULL || \valid(r);
  @ assigns \nothing;
  @ behavior zero:
  @   assumes r == NULL;
  @   ensures \result == *i;
  @ behavior normal:
  @   assumes \valid(r);
  @   ensures \result == (*r);
  @*/
int f3(int *r, int* i) {
  int x = *i;
  if (r)
    x = *r;

  return x;
}

