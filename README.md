# symbolic-loop-splitting


## High-Level Idea:

```
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
```

In this example, `a` can be represented as the CR `{30, +, 1}` and `i` as `{0, +, 2}`.
This implies that they can be represented by two lines: 
1. `x + 30`  
2. `2x + 0`  

These two lines intersect at:
```
2x + 0 = x + 30
  -> x := 30 (number of iterations)
  -> y := 60 (value of 'i' and 'a' during this iteration)
```  

After using this intersection point to split the loop, we have:

```
int f_opt(int n) {
   int s = 0;
   int a = 30;

   //first split
   //dead loop
   int firstSplit = (n<60?n:60);
   for (int i = 0; i<firstSplit; i+= 2) {
      //if ( a < i ) would always be false
      //  s += i; // dead
      a++;
   }

   //second split
   for (int i = 60; i<n; i+=2) {
     //if ( a < i ) would always be true
     s += i;
     a++;
   }
  return s;
}
```

### General case:

```
  loop : 
    if {b1, +, a1} < {b2, +, a2} :
      <body>
```
For this general case, we will have the following line equations: 
1. `a1*x + b1`
2. `a2*x + b2` 

Such that their intersection point is:
```
a1*x + b1 = a2*x + b2
(a1-a2)*x = (b2-b1)
  -> x := (b2-b1)/(a1-a2)
  -> y := a1*(b2-b1)/(a1-a2) + b1
```
This intersection point can then be used to split the loop.

