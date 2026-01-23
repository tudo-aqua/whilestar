vars:
    int x;
    int z;
    int r;
code:
    extern x 0 .. 100;
    extern z 0 .. 100;
    r := 9;
    print "Testing ExSymExe28", x;
    if (z = x) {
        print "Branch F001", z;
    } else {
        assert (false);
        print "Branch F002", z;
    };
    if (x = r) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };