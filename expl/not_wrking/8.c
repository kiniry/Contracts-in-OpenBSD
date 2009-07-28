//In the assigns clause of g(), parameter p refers to g()'s argument, not to the global variable p.

//This problem can be circumvented using ghost variables.


typedef struct { int a; } las;

las * p;

//@ghost las ** const PP=&p;

/*@
requires \valid(p)
assigns p->a
@*/

void f() { p->a = 5; }

/*@
assigns *PP->a
@*/

void g(int * p) { f(); }
