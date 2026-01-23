vars:
    int x;
    int y;
    int z;
code:
    extern x -100 .. 100;
    extern z -100 .. 100;
    print "Testing ExSymExe3", x;
    y := 3;
    z := z + 1;
    z := z + 1;
    x := z;
    if (x > 0) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
        assert (false);
    };
    if (y > 0) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };