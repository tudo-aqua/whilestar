vars:
    int x;
    int y;
    int z;
    int r;
code:
    x := 13000;
    extern z 0 .. 100;
    print "Testing ExSymExe15", x;
    y := 3;
    r := x + z;
    z := (x - y) - 4;
    if (r <= 99) {
        print "Branch F001", z;
        assert (false);
    } else {
        print "Branch F002", z;
    };
    if (x <= z) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };