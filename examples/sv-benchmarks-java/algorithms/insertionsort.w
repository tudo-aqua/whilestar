vars:
    int[10] arr;
    int i;
    int j;
    int x;
pre: (true)
code:
    while (i < 10) {
        arr[i] := 10 - i;
        i := i + 1;
    };

    i := 1;
    while (i < 10) {
        j := i - 1;
        x := arr[i];
        while ((j >= 0) and (arr[j] > x)) {
            arr[j+1] := arr[j];
            j := j - 1;
        };
        arr[j + 1] := x;
        i := i + 1;
    };
post: (arr[0] < arr[1])