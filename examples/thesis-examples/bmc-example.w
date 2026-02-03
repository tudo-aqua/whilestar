vars:
    int x;
    int y;
pre: (x = 0 and y = 0)
code:
    while (x < 5) {
        x := x + 1;
        y := y + x;
    };
post: (y < 10)

