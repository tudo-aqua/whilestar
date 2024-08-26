vars:
  int x;
  int* x1;
  int** x2;
  int*** x3;
  int**** x4;
code:
  x := 0;
  x1 := &x;
  x2 := &x1;
  x3 := &x2;
  x4 := &x3;
  print "",x;
  *x1 := 1;
  print "",x;
  **x2 := 2;
  print "",x;
  ***x3 := 3;
  print "",x;
  ****x4 := 4;
  print "",x;