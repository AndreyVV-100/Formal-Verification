/*@ requires a >= 0 && b > 0;
    requires \valid(r);
    // assigns *r;
    ensures a == b * \result + *r && 0 <= *r < b;
*/
int idiv(int a, int b, int *r) {
    int q = 0;
    int p = a;

    /*@ loop invariant a == b * q + p && (0 <= p <= a);
        loop variant p;
        // loop assigns q, p;
    */
    while (p >= b) {
        q++;
        p -= b;
    }
    *r = p;
    return q;
}
