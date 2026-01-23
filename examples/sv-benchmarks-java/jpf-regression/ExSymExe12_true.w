vars:
    int field;
    int field2;
    int arg;
    int x;
    int y;
code:
    x := 3;
    field := 9;
    extern arg 0 .. 100;
    print "Testing ExSymExe12", arg;
    y := 3;
    field2 := x + arg;
    x := arg - y;
    arg := field2;
    if (arg < x) {
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
