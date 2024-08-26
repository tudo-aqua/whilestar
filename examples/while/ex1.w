vars:
  int x;
  int sum;
pre: (true)
code:
  x := 10;
  sum := 0;
  while(x > 0) invariant(x >= 0) {
    sum := sum + x;
    x := x - 1;
  };
  print "The sum is ", sum;
post: (true)
