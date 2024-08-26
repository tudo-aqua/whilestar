vars:
  int[10] toSort;
  int idx;
  int smallest;
  int cmp;
pre: (true)
code:
  idx := 0;
  while(idx < 10) invariant(idx <= 10) {
    extern toSort[idx] 0 .. 100;
    idx := idx + 1;
  };

  print "Array before sorting:";
  idx := 0;
  while(idx < 10) invariant(idx <= 10) {
    print "Array at $idx is $x", idx, toSort[idx];
    idx := idx + 1;
  };


  smallest := 0;
  while(smallest < 10) invariant(smallest <= 10) {
    cmp := smallest;
    while(cmp < 10) invariant(cmp <= 10) {
      if(toSort[smallest] > toSort[cmp]) {
        swap toSort[smallest] and toSort[cmp];
      } else {
      };
      cmp := cmp + 1;
    };
    smallest := smallest + 1;
  };

  print "Array after sorting:";
  idx := 0;
  while(idx < 10) invariant(idx <= 10) {
    print "Array at $idx is $x", idx, toSort[idx];
    idx := idx + 1;
  };

  idx := 1;
  while(idx < 10) invariant(true) {
    if(toSort[idx-1] > toSort[idx]) {
      fail "Array not sorted toSort[$idx-1] > toSort[$idx]";
    } else {
    };
    idx := idx + 1;
  };

post: (true)
