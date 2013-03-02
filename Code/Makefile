SYSTEM     = x86_sles10_4.1
LIBFORMAT  = static_pic

#Diego
#CPLEXDIR      = /home/drhachmann/cplex/cplex
#CONCERTDIR    = /home/drhachmann/cplex/concert

#mude os dois caminhos abaixo para os caminhos onde o CPLEX foi instalado no seu computador
CPLEXDIR      = /home/igorosberg/ibm/ILOG/CPLEX_Studio124/cplex
CONCERTDIR    = /home/igorosberg/ibm/ILOG/CPLEX_Studio124/concert

CCC = g++ -O3

CCOPT = -m32 -O -fPIC -fno-strict-aliasing -fexceptions -DNDEBUG -DIL_STD

CPLEXLIBDIR   = $(CPLEXDIR)/lib/$(SYSTEM)/$(LIBFORMAT)
CONCERTLIBDIR = $(CONCERTDIR)/lib/$(SYSTEM)/$(LIBFORMAT)

CCLNFLAGS = -L$(CPLEXLIBDIR) -lilocplex -lcplex -L$(CONCERTLIBDIR) -lconcert -m32 -lm -pthread

CONCERTINCDIR = $(CONCERTDIR)/include
CPLEXINCDIR   = $(CPLEXDIR)/include

CCFLAGS = $(CCOPT) -I$(CPLEXINCDIR) -I$(CONCERTINCDIR) 

all: main.o
	$(CCC) $(CCFLAGS) main.o bnc.o -o  bnc $(CCLNFLAGS)

main.o: main.cpp bnc.o
	$(CCC) $(CCFLAGS) main.cpp -o main.o -c $(CCLNFLAGS)

bnc.o: bnc.cpp
	$(CCC) $(CCFLAGS) bnc.cpp -o bnc.o -c  $(CCLNFLAGS)

clean:
	rm *.o
