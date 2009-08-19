// __in_opt i

#pragma JessieIntegerModel(exact)

/*@ requires i == NULL || \valid(i);
  @ assigns \nothing;
  @ behavior zero:
  @   assumes i == NULL;
  @   ensures \result == 0;
  @ behavior normal:
  @   assumes \valid(i);
  @   ensures \result == *i + 1;
  @*/
int in_opt(int *i) {
  if (i)
    return *i + 1;

  return 0;
}

int in_opt_test(int *i) {
  int a = 0;
  int b = in_opt(&a);
  //@ assert b == 1;
  b = in_opt(NULL);
  //@ assert b == 0;
}
