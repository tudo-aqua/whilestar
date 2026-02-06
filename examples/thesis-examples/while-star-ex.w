vars:
    int x;
    int y;
pre: (x = 0)
code:
    extern y 0..2;
    if (y = 1) {
        print "y", y;
        x := 42;
    } else {
        while (y > 0) {
            x := x + y;
        };
    };
post: (x >= 0)