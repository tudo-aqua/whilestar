vars:
  int x;
code:
  extern x 0 .. 10;
post: (x >= 0 and x <= 10)
