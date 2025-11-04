vars:
    int i;
    int j;
code:
    extern i 0..100;
    j := i + 1;
    if (i == j) {
        assert (false);
    } else {
    };
    if (i >= j) {
        assert (false);
    } else {
    };
    if (j > i) {
        assert (true);
    } else {
        assert (false);
    };
    if (j <= i) {
        assert (false);
    } else {
    };
    if (j < i) {
        assert (false);
    } else {
        assert (true);
    };

