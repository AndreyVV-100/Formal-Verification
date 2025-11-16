// В Promela сильная, все всё видят сразу
bool flag[2] = 0;
byte turn = 0;

active [2] proctype P() {
    byte i = _pid;
    assert(i == 0 || i == 1);
    NCS: printf("NCS: %d\n", i);
    SET: flag[i] = 1; turn = i;
    // Семантика: если значение выражения 0, то блокировка
    TST: !(flag[1 - i] == 1 && turn == i);
    CRS: printf("CRS: %d\n", i);
    RST: flag[i] = 0;
    if
    :: goto NCS;
    :: skip
    fi
}

ltl {
    [](!(P[0]@CRS && P[1]@CRS)) && [](P[0]@SET -> <>(P[0]@CRS))
}
