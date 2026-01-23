vars:
    int x;
    int z;
    int r;
code:
    extern x 0 .. 100;
    x := x % 3;
    extern z 0 .. 100;
    z := z % 5;
    r := 9;
    print "Testing ExSymExe29", x;
    if (not (z = x)) {
        print "Branch F001", z;
    } else {
        print "Branch F002", z;
    };
    if (not (x = r)) {
        assert (false);
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };