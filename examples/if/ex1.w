vars:
  int x;
pre: (true)
code:
  x := 10;
  if(x < 100) {
    print "Smaller 100", x;
  } else {
    print "Bigger or equal 100", x;
  };
post: (true)
