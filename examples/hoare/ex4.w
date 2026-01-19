vars:
  int a;
  int b; 
pre:
  (a>=42 and b<=-23)
code:
  extern a 42..100;
  extern b -100..-23;
  while (not (b=0)) invariant ((b<=0) and (a+b>=53)) {
    if (b>=0) {
      b := b-1;
    }
    else {
      b := b+1;    
    };
    a := a+1;
  };
post:
  (a>=53)
