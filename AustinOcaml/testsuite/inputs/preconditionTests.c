#include <stdio.h>

void testme0(int n, int a)
{
	Austin__Assume(2, n >= 0, n < 100);
	for(int i = 0; i < n; i++)
	{
		printf("i = %d\n", i);
	}
	if(a == 3455)
	{
		printf("found\n");
	}
}
