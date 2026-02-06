vars:
    int x;
    int y;
    int z;
    int r;
code:
    x := 3;
    z := 9;
    print "Testing ExSymExe21", x;
    y := 3;
    r := x + z;
    z := (x - y) - 4;
    if (r >= 99) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
    };
    if (x >= z) {
        print "Branch B001", x;
    } else {
        assert (false);
        print "Branch B002", x;
    };