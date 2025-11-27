vars:
    int i;
code:
    i := 0;
    if (not (i = 0)) {
        assert (false);
    } else {
    };
    i := 1;
    if (i = 0) {
        assert (false);
    } else {
    };
    if (i < 0) {
        assert (false);
    } else {
    };
    i := 0;
    if (i > 0) {
        assert (false);
    } else {
    };
    i := 1;
    if (i <= 0) {
        assert (false);
    } else {
    };
    i := -1;
    if (i >= 0) {
        assert (false);
    } else {
    };