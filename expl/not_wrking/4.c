//@ ensures 0 <= \result <= 9;
int any();

int i;
int t[10];

/*@ assigns i,t[\at(i, Post)]
  @ ensures t[i] == \old(t[\at(i,Here)]) + 1;
  @ ensures
  @  \let j = i; t[j] == \old (t[j]) + 1;
  @*/
void f2()
{
 i = any ();
 t[i]++;
}
