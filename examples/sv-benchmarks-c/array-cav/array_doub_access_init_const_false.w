vars:
    int i;
    int N;
    int[12] a;
pre: (i = 0)
code:
    N := 1;
    i := 0;
    while (i <= N) {
        a[(2 * i)] := 0;
        a[(2 * i) + 1] := 0;
        i := i + 1;
    };

    i := 0;
    while (i <= N*2) {
        assert (a[i] >= 0);
        i := i + 1;
    };
post: (a[0] = 1)