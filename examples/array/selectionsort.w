vars:
  int[10] feld;
  int i1;
  int i2;
  int min;
code:
  i1 := 0;
  while(i1<10) {
    extern feld[i1] 0..100;
    print "", feld[i1];
    i1 := i1 + 1;
  };
  print "============";
  i1 := 0;
  while(i1 < 10) {
    min := i1;
    i2 := i1;
    while(i2 < 10) {
      if(feld[i2] < feld[min]) {
        min := i2;
      } else {
      };
      i2 := i2 + 1;
    };
    swap feld[i1] and feld[min];
    i1 := i1 + 1;
  };
  i1 := 0;
  while(i1 < 10) {
    print "", feld[i1]; 
    i1 := i1 + 1;
  };