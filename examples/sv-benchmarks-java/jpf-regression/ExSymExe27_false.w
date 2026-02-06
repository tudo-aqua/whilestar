vars:
    int a;
    int b;
    int x;
    int y;
    int z;
code:
    extern a 0 .. 100;
    extern b 0 .. 100;
    print "Testing ExSymExe27", x;
    x := a;
    y := b;
    z := a;
    x := z;
    y := z + x;
    if (x < y) {
        assert (false);
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
    };
    if (z > 0) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };