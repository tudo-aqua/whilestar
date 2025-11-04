vars:
    int x;
    int y;
    int z;
    int r;
code:
    x := -13;
    extern z 0 .. 100;
    print "Testing ExSymExe14", x;
    y := 3;
    r := x + z;
    x := z - y;
    z := r;
    if (z <= x) {
        print "Branch F001", z;
        assert (false);
    } else {
        print "Branch F002", z;
    };
    if (x <= r) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };