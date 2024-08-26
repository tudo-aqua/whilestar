vars:
  int[100] mem;
  int[100] used;
  int nextFree;
  int n;
  int break;
  int i;
  int sum;
code:
  print "We are now reading dynamically many values.";
  print "The end value is -1";
  while(break = 0) {
    extern n -1..100;
    if(n = -1) {
      break := 1;
    } else {
      if(nextFree < 100) {
        mem[nextFree] := n;
        used[nextFree] := 1;
        nextFree := nextFree + 1;
      } else {
        print "OOM";
      };
    };
  };
  print "We are now summing dynamically many values";
  while(used[i] = 1 and i < 100) {
    sum := sum + mem[i];
    i := i + 1;
  };
  print "The sum is ", sum;