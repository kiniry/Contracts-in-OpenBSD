// __out t, size_t size, assigns only at end by null terminating.

//#pragma JessieIntegerModl(modulo)

/*@ requires
  @   size > 0 && size < INT_MAX && \valid(t) && \valid_range(t,0,size-1);
  @ assigns t[size -1];
  @ behavior zero:
  @   assumes (t == NULL) || (size <= 0);
  @   assigns \nothing;
  @ behavior normal:
  @   assumes size > 0;
*/
void f5(char *t, int size) {
  if ( t && size > 0)
  {
     t[size -1] = '\0';
  }
}

