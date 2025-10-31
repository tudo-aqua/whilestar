vars:
  int a;
  int b;
code:
  a := 1;
  assert (a = 1);
  a := b;
post: (a = 1)
