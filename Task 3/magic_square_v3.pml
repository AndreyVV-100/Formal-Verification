// «Магический квадрат». Расположите в квадрате 3 x 3 (в общем случая, N x N) 9 (N ^ 2)
// последовательных натуральных чисел так, чтобы сумма чисел в каждой строке,
// каждом столбце и на обеих диагоналях была одинакова.

#define N 3
#define N2 (N * N)

byte field[N2];
byte num_filled = 0;

#define field_elem(i, j) field[(i) * N + (j)]

inline sum_line(sum, i_line) {
    sum = 0;
    byte i_elem;
    for (i_elem : 0 .. N-1) {
        sum = sum + field_elem(i_line, i_elem);
    }
}

inline sum_row(sum, i_row) {
    sum = 0;
    byte i_elem;
    for (i_elem : 0 .. N-1) {
        sum = sum + field_elem(i_elem, i_row);
    }
}

inline sum_main_diagonal(sum) {
    sum = 0;
    byte i_elem;
    for (i_elem : 0 .. N-1) {
        sum = sum + field_elem(i_elem, i_elem);
    }
}

inline sum_secondary_diagonal(sum) {
    sum = 0;
    byte i_elem;
    for (i_elem : 0 .. N-1) {
        sum = sum + field_elem(N - 1 - i_elem, i_elem);
    }
}

bool all_sums_are_equal = false;

proctype fill_field(byte i_elem) {
    atomic {
        field[i_elem] = num_filled + 1; num_filled++
    }
}

proctype check_sums() {
    byte sum1, sum2;
    if
    :: num_filled == N2 -> {
        byte i_iter;
        sum_main_diagonal(sum1);
        sum_secondary_diagonal(sum2);
        bool tmp_all_sums_are_equal = (sum1 == sum2);
        for (i_iter : 0 .. N-1) {
            sum_line(sum2, i_iter);
            tmp_all_sums_are_equal = tmp_all_sums_are_equal && (sum1 == sum2);
            sum_row(sum2, i_iter);
            tmp_all_sums_are_equal = tmp_all_sums_are_equal && (sum1 == sum2);
        }

        byte i_line;
        printf("Magic square:\n")
        for (i_line : 0 .. N-1) {
            for (i_iter : 0 .. N-1) {
                printf("%d\t", field_elem(i_line, i_iter));
            }
            printf("\n");
        }

        all_sums_are_equal = tmp_all_sums_are_equal;
    }
    fi
}

init {
    byte i_iter;
    for (i_iter : 0 .. N2-1) {
        field[i_iter] = 0;
    }

    for (i_iter : 0 .. N2-1) {
        run fill_field(i_iter);
    }

    run check_sums();
}

ltl {
    [](!all_sums_are_equal)
}
