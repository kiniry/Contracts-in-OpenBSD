
void f2()
{
	int x = 0;
	int y = 10;
	/*@ loop invariant 0 <= x < 11; */
	while (y > 0)
	{
		x++;
		//@ invariant 0 < x < 11 && x + y == 11;
		y--;
		//@ invariant 0 <= y < 10 && x+y == 10;
	}
}


