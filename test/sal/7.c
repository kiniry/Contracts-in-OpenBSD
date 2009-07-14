// __out t, size_t size can assign any index

//#pragma JessieIntegerModl(modulo)

/*@ requires
  @   size > 0 && size < INT_MAX && \valid(t) && \valid_range(t,0,size-1);
  @ behavior zero:
  @   assumes (t == NULL);
  @   assigns \nothing;
  @ behavior normal:
  @   assumes \valid(t);
  @   assigns t[0..size-1];
  @ disjoint behaviors zero, normal; // not strictly necessary but for completeness. BTW this is a comment for annotation.
*/
void f5(char *t, int size) {
  if ( t && size > 0)
  {
     t[size -1] = 'c';
  }
}

