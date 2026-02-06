vars:
    int a;
    int b;
    int x;
    int y;
    int z;
code:
    a := 3;
    b := 8;
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
        print "Branch B001", x;
    } else {
        assert (false);
        print "Branch B002", x;
    };