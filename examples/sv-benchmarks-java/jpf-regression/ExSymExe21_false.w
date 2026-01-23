vars:
    int x;
    int y;
    int z;
    int r;
code:
    extern x 0 .. 100;
    extern z 0 .. 100;
    z := z % 9;
    print "Testing ExSymExe21", x;
    y := 3;
    r := x + z;
    z := (x - y) - 4;
    if (r >= 99) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
    };
    if (x >= z) {
        assert (false);
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };