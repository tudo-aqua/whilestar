vars:
    int field;
    int field2;
    int x;
    int y;
code:
    x := -13;
    extern field 0 .. 100;
    print "Testing ExSymExe12", field;
    y := 3;
    field2 := x + field;
    x := field - y;
    field := field2;
    if (field < x) {
        print "Branch F001", x;
    } else {
        print "Branch F002", x;
    };
    if (x < field2) {
        print "Branch B001", field2;
    } else {
        print "Branch B002", field2;
        assert (false);
    };
