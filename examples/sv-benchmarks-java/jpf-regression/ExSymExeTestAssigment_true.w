vars:
    int x;
code:
    extern x 0 .. 100;
    print "Testing ExSymExeTestAssigment", x;
    x := 3;
    if (x > 0) {
        print "Branch B001", x;
    } else {
        assert (false);
        print "Branch B002", x;
    };
