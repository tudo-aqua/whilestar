vars:
    int[2] ia;
    int index;
    int i;
code:
    extern index 0 .. 199;
    assert ((index >= 0) and (index < 200));
    ia[index] := 42;
    i := 0;
    while (i < 200) {
        assert (not (ia[i] == 0));
        i := i + 1;
    };
post: (ia[index] == 42)