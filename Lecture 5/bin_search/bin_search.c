/*@
predicate Sorted(long *a, integer n) =
    \forall integer i, j;
        0 <= i <= j < n ==> a[i] <= a[j];
*/

/*@ requires \valid(a + (0..n-1));
    requires Sorted(a, n);
    requires n >= 0;

    ensures -1 <= \result < n;
    ensures \result >= 0
        ==> a[\result] == v;
    ensures \result == -1
        ==> \forall integer k; 0 <= k < n ==> a[k] != v;

    assigns \nothing;
*/
int bin_search(long *a, int n, long v) {
    int l = 0, u = n - 1;
    /*@ loop invariant \forall integer k; 0 <= k < l ==> a[k] < v;
        loop invariant \forall integer k; u < k < n ==> v < a[k];
        // loop invariant Sorted(a, n);
        loop invariant 0 <= l <= n;
        loop invariant -1 <= u < n;
        loop variant n - l + u;
    */
    while (l <= u) {
        // overflow bug: int m = (u + l) / 2;
        int m = l + (u - l) / 2;
        //@ assert l <= m <= u;
        if (a[m] < v) {
            //@ assert \forall integer k; 0 <= k <= m ==> a[k] <= a[m];
            //@ assert \forall integer k; 0 <= k <= m ==> a[k] < v;
            l = m + 1;
        }
        else if (a[m] > v) {
            //@ assert \forall integer k; m <= k < n ==> a[m] <= a[k];
            //@ assert \forall integer k; m <= k < n ==> v < a[k];
            u = m - 1;
        }
        else
            return m;
    }
    return -1;
}
