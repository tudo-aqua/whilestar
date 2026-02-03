vars:
  int x;
  int y;
pre: (true)
code:
  x := 0;
  print "x = ", x;
  extern x 0..1;
  print "x = ", x;
  extern y 1..1;
  print "y = ", y;
post: (y = 1)
