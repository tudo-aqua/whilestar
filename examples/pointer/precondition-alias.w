vars:
  int a;
  int b;
  int *p;
pre: (a = 0)
code:
  p := &b;
  *p := 5;
post: (a = 0)
