#include <stdio.h>

struct test{
        int a;
        char b;
        char *c;
};

void func(int i)
{
	int j = 0;
	int arr2[10];
	/*while(j<i){
		arr2[j] = j;
		j++;
	}*/
	return;
}

int main()
{
	struct test var, *var_ptr, **var_ptr_ptr;
	int arr[10];
	int j = 0, i = 20;
	int *p = &i;
	while(j<i){
		arr[j] = j;
		j++;
	}
	var_ptr = &var;
	var_ptr->a = 10;
	var.b = 'r';
	var_ptr->a += (int)var_ptr->b;
	var_ptr_ptr = &var_ptr;
	func(i);
	return 0;
}
