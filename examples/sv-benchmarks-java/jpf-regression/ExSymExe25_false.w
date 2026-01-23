vars:
    int a;
    int b;
    int x;
    int y;
    int z;
code:
    extern a 0 .. 100;
    extern b 0 .. 100;
    print "Testing ExSymExe25", x;
    x := a;
    y := b;
    z := a;
    y := z + 1;
    z := z + x;
    x := x + 3;
    if (z > 0) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
    };
    if (x > 0) {
        assert (false);
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };