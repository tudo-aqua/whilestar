vars:
    int field;
    int x;
    int y;
code:
    x := -10;
    extern field 0 .. 100;
    print "Testing ExSymExe10", field;
    y := 3;
    x := x * field;
    field := ((-1) * x) + y;
    if (field <= 0) {
        print "Branch F001", field;
    } else {
        print "Branch F002", field;
        assert (false);
    };
    if (x <= 0) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };