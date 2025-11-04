vars:
    int arg;
    int x;
    int y;
    int z;
code:
    extern arg 0 .. 100;
    x := 10 - (arg % 9);
    z := 10 - (arg % 5);
    print "Testing ExSymExe7", x;
    y := 3;
    z := (x - y) - 4;
    if (not (z = 0)) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
        assert (false);
    };
    if (not (y = 0)) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };