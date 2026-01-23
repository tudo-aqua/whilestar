vars:
    int a;
    int b;
    int x;
    int y;
    int z;
code:
    a := 3;
    b := 8;
    print "Testing ExSymExe26", x;
    x := a;
    y := b;
    z := a;
    y := x;
    z := z + 1;
    if (z > 0) {
        print "Branch F001", z;
    } else {
        assert (false);
        print "Branch F002", z;
    };
    if (y > 0) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };