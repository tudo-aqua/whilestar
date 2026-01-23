vars:
    int a;
    int b;
    int result;
    int sum;
    int diff;
    int t;
code:
    extern a 0 .. 200;
    b := 5;
    print "Testing ExSymExeResearch", a;
    result := 0;
    if (((a >= 0) and (a < 100)) and ((b >= 0) and (b < 100))) {
        sum := a + b;
        diff := a - b;
        if (sum > 0) {
            t := a;
        } else {
            t := b;
        };
        if (t < diff) {
            result := t;
        } else {
            result := diff;
        };
    } else {
    };
post: (not (result = (a + b)))