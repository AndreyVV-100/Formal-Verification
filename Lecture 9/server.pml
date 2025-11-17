#define N 3
#define CAP 2
#define MOD 7

chan req = [CAP] of {
    byte, // msg
    byte // id
};

chan resp[N] = [0] of { byte /* resp */ };

active proctype server() {
    byte msg, id
    do
    :: req?msg,id ->
        assert(id < N);
        resp[id]!((msg + 1) % MOD);
    od
}

proctype clients(byte id) {
    assert(id < N);
    byte msg = 0;
    // req!msg,id;
    do
    :: true ->
        ClientSend:
            req!msg,id
            resp[id]?msg;
        ClientRecv:
            skip;
    od
}

active proctype watchdog() {
    do
    :: timeout -> assert(false)
    od
}

init {
    byte id;
    for (id : 0 .. N-1) {
        run clients(id);
    }
}

ltl {
    [](clients[5]@ClientSend -> <>(clients[5]@ClientRecv))
}
