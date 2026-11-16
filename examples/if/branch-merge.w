vars:
  int x;
code:
  x := 0;
  if (x = 0) {
    x := 7;
  } else {
    x := 8;
  };
post: (x = 7)
