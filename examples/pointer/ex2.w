vars:
  int a;
  int b;
  int *x;
  int *y;
pre: (true)
code:
  a := 1;
  b := 1;
  x := &a;
  y := &b;
  print "a = ", a;
  print "b = ", b;
  print "x = ", x;
  print "y = ", y;
  if(x == y) {
    print "Pointers are equal";
  } else {
    print "Pointers are unequal";
  };
  if(*x = *y) {
    print "Values are equal";
  } else {
    print "Values are unequal";
  };
post: (true)
