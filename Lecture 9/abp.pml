#define BUFFER_SIZE 3
#define INVALID_SEQ 255

chan d = [1] of {
    byte, // data
    bool, // checksum (error)
    byte // seq
}; // data

chan a =  [1] of {
    bool, // checksum (error)
    byte // seq
}; // approve

byte send_msg = 0;
byte send_seq = 0;

active proctype P() {
    bool checksum;
    byte recv_seq;
    do
    :: d!send_msg,0,send_seq ->
        Send: printf("P: send %d\n", send_msg);
    :: a?checksum,recv_seq ->
        if
        :: checksum // error
        :: !checksum && recv_seq == send_seq ->
            printf("Next msg\n");
            send_seq = 1 - send_seq;
            send_msg = (send_msg + 1) % BUFFER_SIZE;
        :: else
        fi
    od
}

byte send_ack = INVALID_SEQ;
byte recv_msg = INVALID_SEQ;

active proctype C() {
    bool checksum;
    byte recv_seq;
    do
    :: send_ack != INVALID_SEQ -> a!0,send_ack
    :: d?recv_msg,checksum,recv_seq -> Recv:
        if
        :: checksum
        :: !checksum ->
            RecvOk:
                printf("C: recv %d\n", recv_msg);
                send_ack = recv_seq;
        :: else
        fi
    od
}

active proctype d_media() {
    do
    :: true -> Loss:
        atomic {
            printf("D loss\n");
            d?_,_,_;
        }
    :: true -> Corruption:
        atomic {
            printf("D corruption\n");
            d?_,0,_;
            d!INVALID_SEQ,1,INVALID_SEQ;
        }
    :: true -> Normal:
        atomic {
            printf("D normal\n");
            d?<_,0,_>;
            empty(d);
        }
    od
}

active proctype a_media() {
    do
    :: true -> Loss:
        atomic {
            printf("A loss\n");
            a?_,_;
        }
    :: true -> Corruption:
        atomic {
            printf("A corruption\n");
            a?0,_;
            a!1,INVALID_SEQ;
        }
    :: true -> Normal:
        atomic {
            printf("A normal\n");
            a?<0,_>;
            empty(a);
        }
    od
}

active proctype watchdog() {
    do
    :: timeout -> assert(false)
    od
}

#define LINK_ALIVE(c) []<>(c##_media@Normal)

ltl {
    // [](P@Send -> <>(C@Recv -> <>(C@RecvOk)))
    (LINK_ALIVE(d) && LINK_ALIVE(a)) ->
        []((P@Send && <>C@Recv) -> <>(C@RecvOk && (recv_msg == send_msg)))
}
