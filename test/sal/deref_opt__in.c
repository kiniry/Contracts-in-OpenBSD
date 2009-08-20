// __deref_opt_in

/*@ requires \valid(ppi);
    assigns \nothing;
    behavior zero:
      assumes *ppi == NULL;
      ensures \result == 0;
    behavior normal:
      assumes \valid(*ppi);
      ensures \result == **ppi;
  */
int deref_opt_in(int **ppi) {
  if (*ppi)
  {
	  return **ppi;
  }
  return 0;
}

void deref_opt_in_test()
{
	int a = 5;
	int b;
	int *pa = &a;
	b = deref_opt_in(&pa);
	//@ assert *pa == a;
	//@ assert b == a;
	int *p = NULL;
	int **ppa = &p;

	b = deref_opt_in(ppa);
    //@ assert b == 0;
}


