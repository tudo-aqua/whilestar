vars:
    int x;
pre: (true)
code:
    x := 0;
    while (x < 100) {
        x := x + 1;
    };
post: (x = 100)