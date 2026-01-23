vars:
    int x;
    int z;
    int r;
code:
    x := 3;
    z := 5;
    r := 9;
    print "Testing ExSymExe29", x;
    if (not (z = x)) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
    };
    if (not (x = r)) {
        print "Branch B001", x;
    } else {
        assert (false);
        print "Branch B002", x;
    };