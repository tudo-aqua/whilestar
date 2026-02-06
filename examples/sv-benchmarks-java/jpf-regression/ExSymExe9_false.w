vars:
    int x;
    int y;
    int z;
code:
    x := 10;
    z := 9;
    print "Testing ExSymExe9", x;
    y := 3;
    z := (x - y) - 4;
    if (z < 0) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
        assert (false);
    };
    if (y < 0) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };