vars:
    int field;
    int x;
    int y;
code:
    x := 3;
    extern field 0 .. 100;
    print "Testing ExSymExe11", field;
    y := 3;
    field := (-1) * x;
    x := field * x;
    if (z <= 0) {
        print "Branch F001", field;
    } else {
        print "Branch F002", field;
    };
    if (y <= 0) {
        print "Branch B001", y;
    } else {
        print "Branch B002", y;
        assert (false);
    };