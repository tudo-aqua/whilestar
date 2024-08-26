vars:
  int x;
pre: (x>0)
code:
  extern x 0 .. 10;
post: (x>0)