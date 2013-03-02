#include "bnc.h"
#include <sys/times.h>
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
int main( int argc, char** argv ){
	char* model;
	int time_limit;
	int primal_heuristic;
	char* input_file;
	int nc; //number of cuts
	int md; //maxdeep
	int odd_hole;
	tms buf1, buf2;;
	times(&buf1);
	model = argv[1];
	sscanf( argv[2], "%d", &time_limit );
	sscanf( argv[3], "%d", &primal_heuristic );
	input_file = argv[4];
	
	//sscanf( argv[5], "%d", &nc);
	//sscanf( argv[6], "%d", &md);
	//sscanf( argv[7], "%d", &odd_hole);
	
	BNC bnc( model, time_limit, primal_heuristic, input_file);
	
	bnc.n_cortes = 5;
	bnc.max_deep = 10;
	
	bnc.solve();
	times(&buf2);
	printf("USER_TIME %lf\n",(intmax_t) (buf2.tms_utime - buf1.tms_utime)/100.0);
	return (0);
}
