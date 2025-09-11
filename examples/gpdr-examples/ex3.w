vars:
  int a;
  int b;
pre: (b = 1)
code:
  while (a == 1) {
    extern a 0..1;
    b := b;
  };
post: (b = 1)
