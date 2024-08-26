vars:
  int y;
  int z;
pre: (true)
code:
  extern y 0..100;
  z := y % 2;
  print "y = ", y;
  print "is ";
  if(y%2 = 0) {
    print "even";
  } else {
    print "odd";
  };
post: (true)
