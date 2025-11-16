#define N 5

typedef Rod {
    byte stack[N];
    byte stackTop;
};

Rod rods[3];

#define top(rod) rods[rod].stack[rods[rod].stackTop - 1]
#define isEmpty(rod) (rods[rod].stackTop == 0)

inline isValidMove(i, j) {
    rods[i].stackTop > 0 && (isEmpty(j) || top(i) < top(j))
}

inline move(i, j) {
    atomic {
        printf("move %d -> %d (%d)\n", i, j, top(i));
        rods[j].stackTop++;
        top(j) = top(i);
        rods[i].stackTop--;
    }
}

proctype main() {
    do
    :: isValidMove(0, 1) -> move(0, 1);
    :: isValidMove(0, 2) -> move(0, 2);
    :: isValidMove(1, 0) -> move(1, 0);
    :: isValidMove(1, 2) -> move(1, 2);
    :: isValidMove(2, 0) -> move(2, 0);
    :: isValidMove(2, 1) -> move(2, 1);
    od
}

init {
    byte i;
    for (i : 0 .. N-1) {
        rods[0].stack[i] = N - i;
    }

    rods[0].stackTop = N;
    rods[1].stackTop = 0;
    rods[2].stackTop = 0;

    run main();
}

ltl {
    !(<>(rods[2].stackTop == N))
}
