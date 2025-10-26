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
predicate arrays_are_equal{L}(int *arr1, int *arr2, integer b, integer e) =
    \forall integer i; b <= i < e ==> \at(arr1[i], L) == \at(arr2[i], L);
*/

/*@
predicate swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =
    b <= i < e && b <= j < e &&
    \at(a[i], L1) == \at(a[j], L2) &&
    \at(a[j], L1) == \at(a[i], L2) &&
    \forall integer k; b <= k < e && k != j && k != i ==>
    \at(a[k], L1) == \at(a[k], L2);

axiomatic permutation_axioms {

inductive permutation{L1,L2}(int* a, integer b, integer e) {
    case reflexive{L1}:
        \forall int* a, integer b,e ; permutation{L1,L1}(a, b, e);

    case swap{L1,L2}:
        \forall int* a, integer b,e,i,j ;
            swap_in_array{L1,L2}(a,b,e,i,j) ==> permutation{L1,L2}(a, b, e);

    case transitive{L1,L2,L3}:
        \forall int* a, integer b,e ;
            permutation{L1,L2}(a, b, e) && permutation{L2,L3}(a, b, e) ==>
            permutation{L1,L3}(a, b, e);
 }

    axiom equivalence{L1, L2}:
        \forall int *arr1, int *arr2, integer b, e;
            arrays_are_equal{L1}(arr1, arr2, b, e) &&
            arrays_are_equal{L2}(arr1, arr2, b, e) &&
            permutation{L1, L2}(arr1, b, e) ==>
            permutation{L1, L2}(arr2, b, e);
}

// Unfortunately inductive definition is incorrect and there is no way
// to prove equivalence as a lemma
//
// lemma equivalence{L1, L2}:
//     \forall int *arr1, int *arr2, integer b, e;
//         arrays_are_equal{L1}(arr1, arr2, b, e) &&
//         arrays_are_equal{L2}(arr1, arr2, b, e) &&
//         permutation{L1, L2}(arr1, b, e) ==>
//         permutation{L1, L2}(arr2, b, e);
*/

/*@ 
    requires \valid(arr + (0..n-1));

    ensures sorted(\at(arr, Post), n);
    ensures permutation{Pre, Post}(arr, 0, n);

    assigns arr[0 .. n-1];
*/
void shell_lr(int *arr, int n) {
    int i, j, tmp, gap;
    /*@ loop invariant permutation{LoopEntry, Here}(arr, 0, n);
        loop invariant 0 <= gap <= n / 2 < n || n <= 0 && gap <= 0;
        loop invariant (gap > 0) || (\forall integer k; 1 <= k < n ==> arr[k - 1] <= arr[k]);
        loop variant gap + 1;
    */
    for (gap = n / 2; gap > 0; gap /= 2) {
        //@ assert n > 0;

        /*@ loop invariant permutation{LoopEntry, Here}(arr, 0, n);
            loop invariant gap <= i <= n;
            loop invariant \forall integer k; gap <= k < i ==> arr[k - gap] <= arr[k];
            loop variant n + 1 - i;
        */
        for (i = gap; i < n; ++i) {
            /*@ ghost
                int int_max = 2147483647;
                //@ assert 0 < n <= int_max;
                int new_arr[2147483647];
                //@ assert \valid(new_arr + (0..int_max-1));

                /@
                    loop invariant 0 <= l <= n <= int_max;
                    loop invariant arrays_are_equal{Here}((int *) new_arr, arr, 0, l);
                    loop variant n + 1 - l;
                @/
                for (int l = 0; l < n; l++)
                    new_arr[l] = arr[l];

                //@ assert arrays_are_equal{Here}((int *) new_arr, arr, 0, n);
            */

            tmp = arr[i];
            /*@ loop invariant 0 <= j <= i < n;
                loop invariant \forall integer k; gap <= k < i ==> arr[k - gap] <= arr[k];
                loop invariant arr[i] >= tmp;
                loop invariant arr[j] >= tmp;
                loop invariant arr[i] >= arr[j];
                loop invariant i == j || arr[i - gap] <= arr[i];

                loop invariant arrays_are_equal{Here}((int *) new_arr, arr, 0, j);
                loop invariant arrays_are_equal{Here}((int *) new_arr, arr, j + 1, n);
                loop invariant new_arr[j] == tmp;
                loop invariant permutation{LoopEntry, Here}((int *) new_arr, 0, n);

                loop variant j + gap;
            */
            for (j = i; j >= gap && arr[j - gap] > tmp; j -= gap) {
                arr[j] = arr[j - gap];
                //@ assert arr[j] > tmp;
                /*@ ghost
                    new_arr[j] = new_arr[j - gap];
                    //@ assert arrays_are_equal{Here}((int *) new_arr, arr, 0, n);
                    new_arr[j - gap] = tmp;
                    //@ assert swap_in_array{LoopCurrent, Here}((int *) new_arr, 0, n, j, j - gap);
                */
            }
            arr[j] = tmp;
            //@ assert \forall integer k; gap <= k <= i ==> arr[k - gap] <= arr[k];
            //@ assert arrays_are_equal{Here}((int *) new_arr, arr, 0, n);
        }
        //@ assert \forall integer k; gap <= k < n ==> arr[k - gap] <= arr[k];
    }
}
