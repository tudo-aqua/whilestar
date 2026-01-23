vars:
    int x;
    int y;
    int z;
code:
    extern x -100 .. 100;
    extern z -100 .. 100;
    print "Testing ExSymExe5", x;
    y := 3;
    z := (x + y) + 4;
    if (z >= 0) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
    };
    if (x >= 0) {
        print "Branch B001", x;
        assert (false);
    } else {
        print "Branch B002", x;
    };