#include <stdio.h>

struct test{
	int a;
	char b;
	char c;
};

int main()
{
	struct test k, *kptr, **dkptr;
	kptr = &k;
	kptr->a = 10;
	kptr->b = '0';
	k.c = '1';
//	dkptr = &kptr;
	int i = 0;
//	&i = NULL;
//	int j=i;
//	int *p = &i;
//	*p = 10;
//	int k = &j;
//	scanf("%d",&i);
//	&j = &i;
	//int *q = &j;
//	int **q = &p;
//	{
//		int i;
		char arr[5];
		//while(1)
		for(i = 0; i<4; i++){
			arr[i] = kptr->c;
			*(arr+i) = k.b;
		}
//	}
//	{
//		char arr2[15];
//	}
	//   int b;
	//   int *p, *q;
	//   a = 10;
	//   b = 20;
	//   b = 20;
	//   p = &a;
	//   q = &b;
}
