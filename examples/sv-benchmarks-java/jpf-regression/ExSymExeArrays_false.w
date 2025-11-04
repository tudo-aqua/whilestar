vars:
    int[1] a;
    int x;
code:
    x := -3;
    print "Testing ExSymExeArrays", x;
    a[0] := x;
    if (a[0] >= 0) {
        print "Branch >=0", z;
    } else {
        assert (false);
        print "Branch <0", z;
    };
