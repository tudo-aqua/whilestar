vars:
    int x;
    int y;
    int z;
code:
    x := 3;
    z := 5;
    print "Testing ExSymExe6", x;
    y := 0;
    x := z - y;
    if (not (z = 0)) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
        assert (false);
    };
    if (not (x = 0)) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };