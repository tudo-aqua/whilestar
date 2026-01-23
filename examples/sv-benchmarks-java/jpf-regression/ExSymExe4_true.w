vars:
    int x;
    int y;
    int z;
code:
    x := 3;
    z := 5;
    print "Testing ExSymExe4", x;
    y := 3;
    x := z + y;
    if (z >= 0) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
        assert (false);
    };
    if (x >= 0) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };