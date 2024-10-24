vars:
  int x;
  int y;
pre: (true)
code:
  extern x 0..20;
  if(x % 2 = 0) {
    y := x;
  } else {
    y := x + 1;
  };
  assert (y % 2 = 0);
post: (true)
