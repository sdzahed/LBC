#include<stdio.h>
#include<unistd.h>

void f() {
	struct X {
		int a;
		double b;
	};

	struct Y {
		char *p;
		struct X x;
	} obj;

	struct Y* y = &obj;
	*y->p = 'a';
}

int main()
{
	f();
}


