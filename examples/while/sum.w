vars:
  int n;
  int i;
  int sum;
pre: (n = 0 and (i = 0 and sum = 1))
code:
  extern n 0 .. 100;
  i:= 0;
  sum := 0;
  while(i < n) invariant ((sum = ((i * (i+1))/2)) and (not (n < i))){
    i:= i + 1;
    sum := sum + i;
    assert (i <= n);
  };
  assert (n = i);
post: (sum = ((n * (n+1))/2))