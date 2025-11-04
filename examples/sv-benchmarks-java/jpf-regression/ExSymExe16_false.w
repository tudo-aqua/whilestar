vars:
    int x;
    int y;
    int z;
code:
    x := 300;
    extern z 0 .. 100;
    print "Testing ExSymExe16", x;
    y := 3;
    x := z - y;
    if (z == 0) {
        print "Branch F001", z;
        assert (false);
    } else {
        print "Branch F002", z;
    };
    if (x == 0) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };