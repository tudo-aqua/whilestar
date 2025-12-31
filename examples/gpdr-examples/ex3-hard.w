vars:
  int a;
  int b;
code:
  b := 1;
  while (a == 0) {
    extern a 0..1;
    b := b;
  };
post: (b = 1)
