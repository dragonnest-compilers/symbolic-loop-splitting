#include <stdio.h>

int f(int n) {
  int s = 0;
  for (int i = 0; i<n; i++) {
    s+=i;
    n--;
  }
  return s;
}

int main() {
  printf("%d\n",f(120));
  return 0;
}
