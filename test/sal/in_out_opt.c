// __inout_opt o

#pragma JessieIntegerModel(exact)



/*@ requires o == NULL || \valid(o);

  @ behavior zero:
  @   assumes o == NULL;
  @   assigns \nothing;
  @ behavior normal:
  @   assumes \valid(o);
  @   assigns *o;
  @   ensures *o == \old(*o) + 1;
  @*/
void in_out_opt(int *o) {
  if (o)
  {
    *o += 1;
  }
}

void in_out_opt_test() {
  int a = 5;
  out_opt(&a);
  //@ assert a != 5;
  out_opt(NULL);
  //@ assert a == 6;
}
