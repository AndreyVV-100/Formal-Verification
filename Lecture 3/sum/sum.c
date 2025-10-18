/*@
logic integer Sum(int *a, integer lo, integer hi) =
    (hi > lo) ? a[lo] + Sum(a, lo + 1, hi) : 0;

lemma SumNext:
    \forall int *a, integer lo, hi, s;
        s == Sum(a, lo, hi)
        && lo <= hi
            ==> (s + a[hi]) == Sum(a, lo, hi + 1);
*/

/*@ requires \valid(a + (0..n-1));
    requires n >= 0;
    ensures \result == Sum(a, 0, n);
*/
int sum(int *a, int n) {
    int s = 0;
    /*@ loop invariant s == Sum(a, 0, i);
        loop invariant 0 <= i <= n;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        s += a[i];
        //@ assert s == Sum(a, 0, i + 1);
    }
    return s;
}