// Миссионеры и людоеды: как wgc, но лодка на двоих, а если миссионеров
// на берегу меньше, чем каннибалов, то миссионеров съедают

#define N 3

bool boat = 0; // false == left side
int lM = N; // leftMissioners
int lC = N; // leftCannibals

#define UNSAFE (((lC > lM) && lM && boat) || ((N - lC > N - lM) && (lM != N) && !boat))
#define SAFE !UNSAFE

inline moveOneKind(x, n) {
    atomic {
        x = (boat -> x + n : x - n);
        boat = !boat;
    }
}

inline moveBoth() {
    atomic {
        lM = (boat -> lM + 1 : lM - 1);
        lC = (boat -> lC + 1 : lC - 1);
        boat = !boat;
    }
}

inline canMoveOneKind(x, n) {
    (boat -> N - x >= n : x >= n) && n >= 0 && n < N
}

inline canMoveBoth() {
    (boat -> lM < N && lC < N : lM && lC)
}

active proctype main() {
    do
    :: canMoveBoth() -> moveBoth(); printf("Both\n");
    :: canMoveOneKind(lC, 1) -> moveOneKind(lC, 1); printf("1 Cannibal\n");
    :: canMoveOneKind(lC, 2) -> moveOneKind(lC, 2); printf("2 Cannibals\n");
    :: canMoveOneKind(lM, 1) -> moveOneKind(lM, 1); printf("1 Missioner\n");
    :: canMoveOneKind(lM, 2) -> moveOneKind(lM, 2); printf("2 Missioners\n");
    od
}

ltl {
    !(SAFE U (boat && lM == 0 && lC == 0))
}
