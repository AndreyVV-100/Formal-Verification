// Есть препроцессор, как в C
#define N 5

// active делает процесс точкой входа
active [N] proctype main() {
    printf("hello, world %d\n", _pid);
}

// Настоящая точка входа
init {
    printf("init: %d\n", _pid)
    run main();
}
