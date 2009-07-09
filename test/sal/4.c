// __in t, size_t size


/*@ requires
  @   size > 0 && \valid(t) && \valid_range(t,0,size-1);
  @ assigns \nothing;
@*/
void f4(char *t, int size) {
  if ( t && size > 0)
  {
     char n;
     n = t[size -1];
  }
}

