vars:
  int x;
  int y;
  int z;
pre: (true)
code:
  x := 10;
  y := 0;
  z := 0;
  while(y < x) invariant(y == z) {
    y := y + 1;
    z := z + 1;
    assert(y == z);
  };
post: ((x == y) and (y == z))
