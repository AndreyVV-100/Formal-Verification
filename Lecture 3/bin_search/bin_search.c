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
    while (l <= u) {
        int m = (u + l) / 2;
        if (a[m] < v)
            l = m + 1;
        else if (a[m] > v)
            u = m - 1;
        else
            return m;
    }
    return -1;
}
