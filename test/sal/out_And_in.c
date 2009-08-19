// __out o, __in i

/*@ requires \valid(i) && \valid(o);
  @ assigns *o;

  @ ensures *o == *i;
*/
void OutAndIn(int *i, int *o) {
  *o = *i;
}

void OutAndIn_test()
{
	int a = 5;
	int b = 0;
	OutAndIn(&a, &b);
	//@ assert a == b;
}
