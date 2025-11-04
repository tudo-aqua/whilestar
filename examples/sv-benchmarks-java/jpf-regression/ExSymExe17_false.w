vars:
    int x;
    int y;
    int z;
code:
    x := 4;
    z := 0;
    print "Testing ExSymExe17", x;
    y := 0;
    z := (x - y) - 4;
    if (z == 0) {
        print "Branch F001", z;
        assert (false);
    } else {
        print "Branch F002", z;
    };
    if (x == 0) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };