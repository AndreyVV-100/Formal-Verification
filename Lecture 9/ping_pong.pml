#define N 10

chan c = [1] of {int, int}; // addr, message

proctype P(int id) {
    int x;
    if
    :: (id == 0) -> c!1,0
    :: else
    fi

    do
    :: c?eval(id),x -> x = (x + 1) % N;
                       c!(1 - id),x;
                       printf("send[%d] = %d\n", id, x);
    od
}

active proctype watchdog() {
    do
    :: timeout -> assert(false)
    od
}

init {
    run P(0);
    run P(1);
}
