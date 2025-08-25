vars:
  int x;
pre: (true)
code:
  x := 10;
  while(x < 100) invariant(x <= 100) {
    x := x + 1;
  };
post: (x == 100)
