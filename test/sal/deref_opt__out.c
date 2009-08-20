// __deref_opt_out

/*@ requires \valid(ppo) && (\valid(*ppo) || *ppo == NULL);
    behavior zero:
      assumes *ppo == NULL;
      assigns \nothing;
      ensures \result == 0;
    behavior normal:
      assumes \valid(*ppo);
      assigns **ppo;
      ensures **ppo == 1;
      ensures \result == 1;
  */
int deref_opt_out(int **ppo) {
  if (*ppo)
  {
	  **ppo = 1;
	  return 1;
  }
  return 0;
}

void deref_opt_out_test()
{
	int a = 0;
	int b;
	int *pa = &a;
	b = deref_opt_out(&pa);
	//@ assert *pa == a;
	//@ assert a == 1;
	//@ assert b == 1;
	int *p = NULL;
	int **ppa = &p;
	b = deref_opt_out(ppa);
    //@ assert b == 0;
}


