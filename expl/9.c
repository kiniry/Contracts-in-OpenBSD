//@ predicate non_null(void *p) = p != 0;
#define NON_NULL __declspec(non_null)
char*NON_NULL f(char *NON_NULL x) {

//@ assert x != 0;

return x;

}

//@ predicate range(integer i, integer lb, integer rb) = lb <= i <= rb;

#define RANGE(a,b) __declspec(range(a,b))

int RANGE(-5,15) f2(int RANGE(0,5) x, int RANGE(-5,10) y) {

//@ assert 0 <= x <= 5;

//@ assert -5 <= y <= 10;

return x + y;

}
