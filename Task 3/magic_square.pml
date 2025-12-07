// WARNING: The solution isn't working. Use v2 or v3 instead of it.
// «Магический квадрат». Расположите в квадрате 3 x 3 (в общем случая, N x N) 9 (N ^ 2)
// последовательных натуральных чисел так, чтобы сумма чисел в каждой строке,
// каждом столбце и на обеих диагоналях была одинакова.

#define N 3
#define N2 (N * N)

byte field[N2];
byte num_filled = 0;

#define field_elem(i, j) field[(i) * N + (j)]

proctype fill_square() {
    byte last_free = 0, i_iter = 0;
    do
    :: num_filled == N2 -> break
    :: else -> {
        i_iter = 0;
        do
        :: i_iter < N2 -> {
            if
            :: field[i_iter] == 0 -> {
                    if
                    :: field[i_iter] = num_filled + 1; num_filled = num_filled + 1; break;
                    :: last_free = i_iter; i_iter = i_iter + 1;
                    fi
                }
            :: true -> i_iter < N2 -> i_iter = i_iter + 1;
            fi
        }
        :: else -> field[last_free] = num_filled + 1; num_filled = num_filled + 1;
        od
    }
    od
}

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
        all_sums_are_equal = tmp_all_sums_are_equal;
    }
    fi
}

init {
    byte i_line, i_row;
    for (i_line : 0 .. N-1) {
        for (i_row : 0 .. N-1) {
            field_elem(i_line, i_row) = 0;
        }
    }

    run fill_square();
    run check_sums();
}

ltl {
    !(num_filled < N2 U all_sums_are_equal)
}
