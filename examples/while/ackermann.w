vars:
  int[10] k;
  int[10] n;
  int i;
  int recDepth;
  int[10] a;
code:
  i := 0;
  while(i < 10) {
    k[i] := -1;
    n[i] := -1;
    a[i] := -1;
    i := i + 1;
  };
  extern i 0..10;
  k[0] := i;
  n[0] := i;
  recDepth := 1;
  while(recDepth > 0) {
    i := recDepth - 1;
    if((k[i] = 1) and (n[i] >= 1)) {
      a[i] := 2 * n[i];
      k[i] := -1;
      n[i] := -1;
      recDepth := recDepth - 1;
    } else {
    };
    if((k[i] >= 2) and (n[i] = 1)) {
      a[i] := 2;
      k[i] := -1;
      n[i] := -1;
      recDepth := recDepth - 1;
    } else {
    };
    if((k[i] >= 2) and (n[i] >= 2)) {
      if(a[i+1] = -1) {
        k[i+1] := k[i];
        n[i+1] := n[i] - 1;
        a[i] := -2;
        recDepth := recDepth + 1;
      } else {
      	if(a[i] = -2) {
          k[i+1] := k[i] - 1;
          n[i+1] := a[i+1];
          a[i+1] := -1;
          a[i] := -1;
          recDepth := recDepth + 1;
        } else {
          a[i] := a[i+1];
          k[i+1] := -1;
          n[i+1] := -1;
          a[i+1] := -1;
          recDepth := recDepth - 1;
        };
      };
    } else {
    };
  };
  print "", a[0];