vars:
    int x;
    int y;
    int z;
    int r;
code:
    x := 3;
    z := 9;
    print "Testing ExSymExe18", x;
    y := 3;
    x := x * r;
    z := z * x;
    r := y * x;
    if (z > x) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
        assert (false);
    };
    if (x > r) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };