vars:
    int x;
    int y;
    int z;
    int r;
code:
    x := 3;
    z := 9;
    print "Testing ExSymExe20", x;
    y := 3;
    r := x + z;
    x := z - y;
    z := r;
    if (z >= x) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
    };
    if (x >= r) {
        assert (false);
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };