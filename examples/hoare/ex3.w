vars:
  int x;
  int s;
  int i;
code:
  x:=0;
  s := 0;
  i := 10;
  extern i 1..100;
  print "i: ", i;
  while(x <= i) invariant (((s = ((x*(x-1))/2)) and (i > 0)) and (x <= i+1)) {
    s := s + x;
    x:=x+1;
  };
  print "Sum to $ is $", x,s;
post:
  ((x=(i+1)) and (s=((i*(i+1))/2)))

