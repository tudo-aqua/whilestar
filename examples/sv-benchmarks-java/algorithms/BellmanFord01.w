vars:
    int v;
    int[100] d;
    int[10] dist;
    int i;
    int j;
    int k;
    int tmp;
    int relaxed;
pre: (true)
code:
    v := 10;
    while (i < v) {
        j := 0;
        while (j < v) {
            print "l2", j;
            if (i == j) {
            } else {
                extern tmp 0 .. 16;
                d[(i*v)+j] := tmp;
            };
            j := j + 1;
        };
        i := i + 1;
    };
    print "a", i;
    i := 0;
    while (i < v) {
        dist[i] := 100;
        i := i+1;
    };

    dist[0] := 0;
    relaxed := 1;
    while (k < v and relaxed == 1) {
        relaxed := 0;
        i := 0;
        while (i < v) {
            j := 0;
            while (j < v) {
                if (i == j) {
                } else {
                    if (dist[i] == 100) {
                    } else {
                        if (dist[j] > dist[i] + d[(i*v)+j]) {
                            dist[j] := dist[i] + d[(i*v)+j];
                            relaxed := 1;
                        } else {
                        };
                    };
                };
                j := j+1;
            };
            i := i + 1;
        };
        k := k+1;
    };
    print "b", v;

    i := 0;
    while (i < v) {
        assert (dist[i] <= 100);
        i := i+1;
    };
post: (dist[5] <= 100)