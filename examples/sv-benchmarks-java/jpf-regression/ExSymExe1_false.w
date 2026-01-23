vars:
    int x;
    int y;
code:
    extern x 0 .. 100000;
    x := x % 1000;
    extern y 0 .. 100000;
    y := y % 50;
    print "Testing ExSymExe1", x;
    x := y;
    y := y + 1;
    if (y > 0) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
        assert (false);
    };
    if (x > 0) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
        assert (false);
    };