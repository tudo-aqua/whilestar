vars:
    int x;
    int y;
    int z;
    int r;
code:
    extern x 0 .. 100;
    extern z 0 .. 100;
    print "Testing ExSymExe19", x;
    y := 3;
    x := z + r;
    z := y * x;
    r := -z;
    if (x > 99) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
        assert (false);
    };
    if (r > z) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };