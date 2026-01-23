vars:
    int x;
    int y;
    int z;
    int p;
code:
    extern x 0 .. 100;
    extern z 0 .. 100;
    x := x % 3;
    z := z % 5;
    print "Testing ExSymExe8", x;
    y := 3;
    p := 2;
    x := z - y;
    z := z - p;
    if (z < 0) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
        assert (false);
    };
    if (x < 0) {
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };