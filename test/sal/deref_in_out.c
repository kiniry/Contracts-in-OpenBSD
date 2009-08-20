// __deref_in and deref_out

#pragma JessieIntegerModel(exact)


/*@ requires \valid(ppi) && \valid(ppo) && \valid(*ppi) && \valid(*ppo);
  @ assigns **ppo;

  @ ensures **ppo == **ppi;
*/
void deref_OutAndIn(int **ppi, int **ppo) {
  **ppo = **ppi;
}

void deref_OutAndIn_test()
{
	int a = 5;
	int b = 0;
	int *pb = &b;
	int *pa = &a;
	deref_OutAndIn(&pa, &pb);
	//@ assert *pa == a;
	//@ assert *pb == a;
}
