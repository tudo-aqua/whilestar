vars:
    int field;
    int arg;
    int x;
    int y;
code:
    extern arg 0 .. 10000;
    x := 3;
    field := arg % 100;
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
        assert (false);
    } else {
        print "Branch B002", y;
    };