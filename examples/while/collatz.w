vars:
  int x;
  int steps;
code:
  extern x 0..1000;
  steps := 0;
  while(not (x = 1)) {
    steps := steps + 1;
    print "x:=", x;
    if(x % 2 = 0) {
      x := x/2;
    } else {
      x := (3*x) + 1;
    };
  };
  print "Reached 1 in $1 steps", steps;