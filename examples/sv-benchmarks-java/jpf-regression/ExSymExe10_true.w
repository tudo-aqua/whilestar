vars:
    int field;
    int rand;
    int x;
    int y;
code:
    x := 3;
    field := 9;
    extern rand 0 .. 10;
    if (rand == 2) {
        print "Testing ExSymExe10", field;
        y := 3;
        x := x * field;
        field := ((-1) * x) + y;
        if (field <= 0) {
            print "Branch F001", field;
        } else {
            print "Branch F002", field;
            assert (false);
        };
        if (x <= 0) {
            print "Branch B001", x;
        } else {
            print "Branch B002", x;
        };
    } else {
    };
post: (true)