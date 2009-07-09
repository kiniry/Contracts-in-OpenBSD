// __out t, size_t size, assigns only at end by null terminating. (No behaviors)

//#pragma JessieIntegerModl(modulo)

/*@ requires
  @   size > 0 && size < INT_MAX && \valid(t) && \valid_range(t,0,size-1);
  @ assigns t[size -1];
*/
void f5(char *t, int size) {
  t[size -1] = '\0';}

