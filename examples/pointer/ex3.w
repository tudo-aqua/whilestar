vars:
  int *x;
  int *y;
pre: (true)
code:
  if(x == y) {
    print "Pointers are equal";
  } else {
    print "Pointers are unequal";
  };
post: (true)
