// __out r, __in i
/*@ requires \valid(i);
  @ requires r == NULL || \valid(r);
  @ assigns *r;
  @ behavior zero:
  @   assumes r == NULL;
  @   assigns \nothing;
  @   ensures \result == -1;
  @ behavior normal:
  @   assumes \valid(r);
  @   assigns *r;
  @   ensures *r == *i;
  @   ensures \result == 0;
  @*/
int f(int *r, int* i) {
  if (!r)
    return -1;
  *r = *i;

  return 0;
}

