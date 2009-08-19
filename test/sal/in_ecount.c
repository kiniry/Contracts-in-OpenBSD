// __in_ecount(size) t

/*@ requires
  @   size > 0 && \valid_range(t,0,size-1);
  @ assigns \nothing;

  @ ensures \result == t[size-1];
@*/
char in_ecount(char *t, int size) {
  return t[size -1];
}

void in_ecount_test() {
  char a[] = "test";
  char b = in_ecount(a, 5);
  //@ assert b == '\0';
  char b = in_ecount(a, 4);
    //@ assert b == 't';
}
