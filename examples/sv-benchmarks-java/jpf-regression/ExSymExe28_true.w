vars:
    int x;
    int z;
    int r;
code:
    x := 3;
    z := 5;
    r := 9;
    print "Testing ExSymExe28", x;
    if (z = x) {
        assert (false);
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
    };
    if (x = r) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };