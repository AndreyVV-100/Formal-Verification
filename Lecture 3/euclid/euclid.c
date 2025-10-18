/*@ axiomatic GCD {
        logic integer gcd(integer a, integer b);
        axiom gcd_equal:
            \forall integer x;
                (x > 0) ==> gcd(x, x) == x;
        axiom gcd_comm:
            \forall integer x, integer y;
                (x > 0) && (y > 0) ==> gcd(x, y) == gcd(y, x);
        axiom gcd_add:
            \forall integer x, integer y;
                (x > 0) && (y > 0) ==> gcd(x + y, y) == gcd(x, y);
    }
@*/

/*@ requires a > 0 && b > 0;
    ensures \result == gcd(a, b);
*/
int euclid(int a, int b) {
    int x = a;
    int y = b;
    /*@ loop invariant gcd(x, y) == gcd(a, b) && x > 0 && y > 0;
        loop variant \max(x, y);
    */
    while (x != y) {
        if (x > y) x -= y;
        else y -= x;
    }
    return x;
}
