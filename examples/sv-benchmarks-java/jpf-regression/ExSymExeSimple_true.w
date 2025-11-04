vars:
    int a;
    int b;
code:
    extern a -100 .. 200;
    b := a + 1;
    print "Testing ExSymExeSimple", x;
    if (a > b) {
        print ">", a, b;
    } else {
        if (a = b) {
            assert (false);
            print "eq", a, b;
        } else {
            print "<", a, b;
        };
    };
