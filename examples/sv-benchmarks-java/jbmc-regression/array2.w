vars:
    int[1] arr;
    int unknown;
code:
    extern unknown -100 .. 100;
    if (unknown > 0) {
        arr[0] := 1;
    } else {
    };
    if (unknown > 0) {
        assert (arr[0] == 1);
    } else{
    };
post: (unknown <= 0 or arr[0] == 1)

