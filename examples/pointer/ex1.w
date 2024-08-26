vars:
  int x;
  int *y;
pre: (true)
code:
  x := 10;
  y := &x;
  print "x = ", x;
  print "*y = ", *y;
  *y := 11;
  print "x = ", x;
  print "*y = ", *y;
post: (true)
