vars:
    int x;
    int y;
    int z;
    int r;
code:
    extern x 0 .. 100;
    x := x % 3;
    extern z 0 .. 100;
    z := z % 9;
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
        print "Branch B001", x;
    } else {
        assert (false);
        print "Branch B002", x;
    };