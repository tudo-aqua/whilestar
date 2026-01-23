vars:
    int x;
    int y;
    int z;
    int r;
code:
    extern x 0 .. 100;
    extern z 0 .. 100;
    print "Testing ExSymExe13", x;
    y := 3;
    r := x + z;
    z := (x - y) - 4;
    if (r < 99) {
        print "Branch F001", r;
    } else {
        print "Branch F002", r;
    };
    if (x < z) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
        assert (false);
    };