vars:
    int x;
    int y;
    int z;
    int r;
code:
    x := 3;
    extern z 0 .. 100000;
    z := z % 10;
    print "Testing ExSymExe19", x;
    y := 3;
    x := z + r;
    z := y * x;
    r := -z;
    if (x > 99) {
        print "Branch F001", z;
        assert (false);
    } else {
        print "Branch F002", z;
    };
    if (r > z) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };