// __out_opt r, __in i
/*@ requires \valid(i);
  @ requires r == NULL || \valid(r);
  @ behavior zero:
  @   assumes r == NULL;
  @   assigns \nothing;
  @ behavior normal:
  @   assumes \valid(r);
  @   assigns *r;
  @   ensures *r == *i;
  @*/
void f2(int *r, int *i) {
  if (r)
    *r = *i;
}

