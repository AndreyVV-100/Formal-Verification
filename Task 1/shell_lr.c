/*@
// The predicates are equivalent, but it's not trivial to prove it in frama-c
// predicate sorted(int *a, integer n) =
//     \forall integer i, j;
//         0 <= i <= j < n ==> a[i] <= a[j];
predicate sorted(int *a, integer n) =
    \forall integer i;
        0 <= i < n - 1 ==> a[i] <= a[i + 1];
*/

/*@
predicate swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =
    b <= i < e && b <= j < e &&
    \at(a[i], L1) == \at(a[j], L2) &&
    \at(a[j], L1) == \at(a[i], L2) &&
    \forall integer k; b <= k < e && k != j && k != i ==>
    \at(a[k], L1) == \at(a[k], L2);

predicate cyclic_permutation_in_array{L1, L2}(int* a, integer b, integer e, integer gap, integer begin_cycle, integer end_cycle) =
    (
        b <= begin_cycle <= end_cycle < e &&
        (end_cycle - begin_cycle) % gap == 0 &&
        (\forall integer k; b          <= k < begin_cycle                                ==> \at(a[k], L1) == \at(a[k], L2)) &&
        (\forall integer k; end_cycle   < k < e                                          ==> \at(a[k], L1) == \at(a[k], L2)) &&
        (\forall integer k; begin_cycle < k <= end_cycle && (k - begin_cycle) % gap != 0 ==> \at(a[k], L1) == \at(a[k], L2)) &&
        (\forall integer k; begin_cycle < k <= end_cycle && (k - begin_cycle) % gap == 0 ==> \at(a[k], L1) == \at(a[k] - gap, L2)) &&
        \at(a[begin_cycle], L1) == \at(a[end_cycle], L2)
    );

inductive permutation{L1,L2}(int* a, integer b, integer e){
    case reflexive{L1}:
        \forall int* a, integer b,e ; permutation{L1,L1}(a, b, e);

    // case swap{L1,L2}:
    //     \forall int* a, integer b,e,i,j ;
    //         swap_in_array{L1,L2}(a,b,e,i,j) ==> permutation{L1,L2}(a, b, e);

    case cyclic_permutation{L1,L2}:
        \forall int* a, integer b, e, gap, begin_cycle, end_cycle; 
            cyclic_permutation_in_array{L1, L2}(a, b, e, gap, begin_cycle, end_cycle)
            ==> permutation{L1,L2}(a, b, e);

    case transitive{L1,L2,L3}:
        \forall int* a, integer b,e ;
            permutation{L1,L2}(a, b, e) && permutation{L2,L3}(a, b, e) ==>
            permutation{L1,L3}(a, b, e);
 }
*/

/*@ requires \valid(arr + (0..n-1));
    requires n > 0; // TODO

    ensures sorted(\at(arr, Post), n);
    ensures permutation{Pre, Post}(arr, 0, n);

    assigns arr[0 .. n-1];
*/
void shell_lr(int *arr, int n) {
    int i, j, tmp, gap;
    /*@ loop invariant permutation{LoopEntry, Here}(arr, 0, n);
        loop invariant 0 <= gap <= n / 2;
        loop invariant (gap != 0) || (\forall integer k; 1 <= k < n ==> arr[k - 1] <= arr[k]);
        loop variant gap + 1;
    */
    for (gap = n / 2; gap > 0; gap /= 2) {
        /*@ loop invariant permutation{LoopEntry, Here}(arr, 0, n);
            loop invariant gap <= i <= n;
            loop invariant \forall integer k; gap <= k < i ==> arr[k - gap] <= arr[k];
            loop variant n + 1 - i;
        */
        for (i = gap; i < n; ++i) {
            tmp = arr[i];
            /*@ loop invariant 0 <= j <= i < n;
                loop invariant \forall integer k; gap <= k < i ==> arr[k - gap] <= arr[k];
                loop invariant arr[i] >= tmp;
                loop invariant arr[j] >= tmp;
                loop invariant arr[i] >= arr[j];
                loop invariant i == j || arr[i - gap] <= arr[i];
                
                loop invariant i;
                loop invariant (i - j) % gap == 0;
                // loop invariant \forall integer k; 0 <= k < n ==>
                //     \at(arr[k], Here) == \at(arr[k], LoopEntry) && k > i ||
                //     \at(arr[k], Here) == \at(arr[k], LoopEntry) && k <= j ||
                //     \at(arr[k], Here) == \at(arr[k - gap], LoopEntry) && j < k <= i;
                loop invariant \forall integer k; 0 <= k <= j ==> \at(arr[k], Here) == \at(arr[k], LoopEntry);
                // loop invariant (\forall integer k; 0 <= k <= j && \at(arr[k], Here) == \at(arr[k], LoopEntry)) ==> \at(arr[j], Here) == \at(arr[j], LoopEntry);
                loop invariant \at(arr[j], Here) == \at(arr[j], LoopEntry);

                // loop invariant \forall integer k;      k == j ==> \at(arr[k], Here) == \at(arr[k], LoopEntry);
                loop invariant \forall integer k; i <  k <  n ==> \at(arr[k], Here) == \at(arr[k], LoopEntry);
                loop invariant \forall integer k; j <  k <= i && (i - k) % gap == 0 ==> \at(arr[k], Here) == \at(arr[k - gap], LoopEntry);
                loop invariant \forall integer k; j <  k <= i && (i - k) % gap != 0 ==> \at(arr[k], Here) == \at(arr[k], LoopEntry);
                loop variant j + gap;
            */
            for (j = i; j >= gap && arr[j - gap] > tmp; j -= gap) {
                //@ assert \at(arr[j], Here) == \at(arr[j], LoopEntry);
                //@ assert \at(arr[j - gap], Here) == \at(arr[j - gap], LoopEntry);
                arr[j] = arr[j - gap];
                //@ assert arr[j] > tmp;
                //@ assert \at(arr[j], Here) == \at(arr[j - gap], LoopEntry);
            }
            arr[j] = tmp;
            //@ assert 0 <= j <= i < n;
            //@ assert (i - j) % gap == 0;
            //@ assert \forall integer k; gap <= k <= i ==> arr[k - gap] <= arr[k];
            //@ assert \forall integer k; 0 <= k <  j ==> \at(arr[k], Here) == \at(arr[k], LoopCurrent);
            //@ assert \forall integer k; i <  k <  n ==> \at(arr[k], Here) == \at(arr[k], LoopCurrent);
            //@ assert \forall integer k; j <  k <= i && (i - k) % gap == 0 ==> \at(arr[k], Here) == \at(arr[k - gap], LoopCurrent);
            //@ assert \forall integer k; j <  k <= i && (i - k) % gap != 0 ==> \at(arr[k], Here) == \at(arr[k], LoopCurrent);
            //@ assert \at(arr[j], Here) == \at(arr[i], LoopCurrent);
            //@ assert cyclic_permutation_in_array{Here, LoopCurrent}(arr, 0, n, gap, j, i);
        }
        //@ assert \forall integer k; gap <= k < n ==> arr[k - gap] <= arr[k];
    }
}
