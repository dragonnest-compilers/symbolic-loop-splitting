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

In this example, using Chains of Recurrences, `a` can be represented by `{30, +, 1}` and `i` by `{0, +, 2}`.
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

### Disjunctions and conjunctions:

Treat `and` and `or` operations.

For example

```
    if {b1, +, a1} < {b2, +, a2} && {c1, +, d1} > {c2, +, d2} :
      <body>
```

we should resolve simbolically when both constraints are true. 

#### High level idea

- Calculate truth intervals for both induction variables
- In case of conjunctions, take interval where both are true
- In case of conjunctions, merge intervals, this will possibly generate multiple loop splits

## References

* [Loop splitting](https://en.wikipedia.org/wiki/Loop_splitting)
* [Line-line intersection](https://en.wikipedia.org/wiki/Line%E2%80%93line_intersection)
* [Chains of recurrences](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.43.8188&rep=rep1&type=pdf)
* [SCEV (LLVM's Framework for Chains of Recurrences)](https://www.youtube.com/watch?v=AmjliNp0_00)
