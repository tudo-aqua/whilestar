vars:
    int i;
    int t;
code:
    i := 99;
    i := i - 1;
    t := i + 2;
    i := t;
    i := i + 3;
    i := i - 3;
    t := i * 2;
    i := t;
    t := i / 3;
    i := t;
    i := i % 34;
    i := (-1) * i;
post: (i  == -32)