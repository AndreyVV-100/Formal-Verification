abp:
	spin -a abp.pml
	gcc pan.c -o pan
	./pan -a -f
# check counterexample:
# 	spin -t abp.pml

server:
	spin -a server.pml
	gcc pan.c -o pan -DNOREDUCE -DNFAIR=3
	./pan -a -f
# check counterexample:
	spin -t server.pml