vars:
    int x;
    int y;
    int z;
code:
    extern x 0 .. 100;
    x := (x % 13) - 13;
    extern z 0 .. 100;
    z := (x % 15) - 15;
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