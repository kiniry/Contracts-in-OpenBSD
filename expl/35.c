// __in struct pointer
typedef struct s
{
  int a;
  int b;
} S;

/*@ requires \valid(ps);
  @ assigns ps->b;
*/
void f6(S *ps)
{
  if (ps)
  {
    if (ps->a == 0)
    {
      ps->b = 0;
    }
    else
    {
      ps->b = 1;
    }
  }
}

