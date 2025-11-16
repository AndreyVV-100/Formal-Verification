proctype euclid(int a, b) {
    int x = a, y = b;
    do
    :: x < y -> y = y - x;
    :: x > y -> x = x - y;
    :: else  -> break;
    od
    printf("gcd(%d, %d) = %d\n", a, b, x);
}

init {
    run euclid(17 * 19, 17 * 5);
}
