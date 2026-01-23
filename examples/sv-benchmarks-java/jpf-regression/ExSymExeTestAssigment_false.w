vars:
    int x;
code:
    extern x -100 .. 100;
    print "Testing ExSymExeTestAssigment", x;
    if (x > 0) {
        assert (false);
        print "Branch B001", x;
    } else {
        print "Branch B002", x;
    };
