vars:
  int x;
  int y;
pre: (true)
code:
  extern x 0..20;
  if(x % 2 = 0) {
    y := x + 1;
  } else {
    y := x;
  };
  assert (y % 2 = 1);
  print "", y;
post: (true)
