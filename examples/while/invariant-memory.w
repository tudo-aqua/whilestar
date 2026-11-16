vars:
  int x;
  int y;
pre: (x = 0)
code:
  y := 0;
  while (y < 3) invariant (x = 0) {
    y := y + 1;
  };
post: (x = 0)
