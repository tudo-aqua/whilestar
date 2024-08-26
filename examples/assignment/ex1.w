vars:
  int x;
pre: (true)
code:
  x := 10;
  print "x = ", x;
  x := 11;
  print "x = ", x;
post: (true)
