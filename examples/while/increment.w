vars:
    int x;
code:
    x := 0;
    while (x < 100) invariant (x % 2 = 0) {
        x := x + 2;
    };
post: (x = 100)