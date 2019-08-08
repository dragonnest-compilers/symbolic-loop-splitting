#include <stdio.h>

int f(int n) {
  int s = 0;
  int a = 30;
  for (int i = 0; i<n; i+= 2) {
    if (a < i)
      s += i;
    a++;
  }
  return s;
}


int main() {
  printf("%d\n",f(120));
  return 0;
}
