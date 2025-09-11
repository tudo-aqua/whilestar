vars:
  int a;
  int b;
pre: (b = true)
code:
  a := b;
post: (a = true)
