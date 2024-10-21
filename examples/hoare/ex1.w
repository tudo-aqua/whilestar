vars:
  int i;
  int j;
  int[3] f;
code:
  extern f[0] 1..10;
  extern f[1] 1..10;
  extern f[2] 1..10;
  print "before", f[0], f[1], f[2];
  while (i < 2) invariant ((i > 0 => f[0] <= f[1]) and (i > 1 => f[1] <= f[2]) ) {
    j := i+1;
    while (j < 3) invariant ((j>=2 => f[0] <= f[1])) {
      if (f[i] > f[j]) {
        swap f[i] and f[j];
      } else {};
      j := j+1;
    };
    i := i+1;
  };
  print "after", f[0], f[1], f[2];
post:
  (f[0] <= f[1] and f[1] <= f[2])