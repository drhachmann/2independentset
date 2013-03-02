#include "bnc.h"
#include <stack>
#include <sys/times.h>
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <algorithm>

typedef vector<pair<int, double> >::iterator itR;

#define TRY_CUTS_MULT 10
#define EPS 0.0000001
int bestIncumbent = -1;
int op1=0;
int op2=0;
int sort_cuts=0;
static int sem_cuts=0;//rodadas sem cortes
int tot_cut_pass=0;
int cut_deep[1000];
int cut_pass[1000];
int cortados[1000];
intmax_t tot_time_cut=0;
int use_odd_cut=0;//usa cortes por ciclo impar
int tot_cuts=0;

int current_deep;

//inicio variaveis globais adicionadas por igor
int user_cuts_applied = 0;
double first_relaxation_value = -1;
double elapsed_time_at_first_node;
clock_t start, end;
double total_elapsed_time;
//fim variaveis globais adicionadas por igor


BNC::BNC( char* mo, int tl, int ph, char* in){
	mod = mo;
	time_limit = tl;
	primal_heuristic = ph;
	
	ifstream in_file( in, ifstream::in );
	
	if( !in_file.is_open() ){
		cout << "Error in file bnc.cpp, constructor BNC: Could not open file " << in << endl ;
		exit(-1);
	}
	
	{
	char line[50];
	in_file.getline( line, 50 );
	}
	
	in_file >> n >> m;
	printf("DIMENSOES %d %d\n", n, m);
	adj = vector<vector<int > >(n);
	
	graph = new int*[n];
	for( int i = 0; i < n; ++i )
		graph[i] = new int[n];
	
	for( int i = 0; i < n; ++i )
		for( int j = 0; j < n; ++j )
			graph[i][j] = 0;
	
	for( int k = 0; k < m; ++k ){
		int i, j;
		in_file >> i >> j;
		--i; --j;
		adj[i].push_back(j);
		adj[j].push_back(i);
		graph[i][j] = 1;
		graph[j][i] = 1;
	}
	
	env = NULL;
	model = NULL;
	variables = NULL;
	constraints = NULL;
	cplex = NULL;
	
	in_file.close();

	input_file = in;	
	out_file_sol = string(in) + string(".sol");
	out_file_est = string(in) + string(".est");

}

BNC::~BNC(){
	
	for( int i = 0; i < n; ++i )
		delete [] graph[i];
	delete [] graph;
	
	delete cplex;
	delete variables;
	delete constraints;
	delete model;
	delete env;
	
}

//set the current_deep variable to the deep of current node
ILONODECALLBACK1( MySelect, int*, deep ){
	*deep = getDepth(0);	
}



int tot_time_heur=0;
int tot_sol_heur=0;
ILOHEURISTICCALLBACK3(Rounddown, IloNumVarArray, vars, int**, graph, vector<vector<int> > &, adj) {
	if( first_relaxation_value == -1 ){
		first_relaxation_value = getBestObjValue();
		elapsed_time_at_first_node = (double)( clock() - start )/(double)CLOCKS_PER_SEC;
	}
	
	
	tms buf1, buf2;
	clock_t t1 = times(&buf1);
	int n = vars.getSize()/2;
	
	IntegerFeasibilityArray feas( getEnv() );
	IloNumArray x( getEnv() );
	
	getFeasibilities( feas, vars );
	getValues( x, vars );
	
	int newobj1 = 0;
	int newobj2 = 0;
	int newx1[2*n];
	int newx2[2*n];
	
	memset(newx1, 0, sizeof(newx1));
	memset(newx2, 0, sizeof(newx2));
	int acc[2*n];
	memset(acc, 0, sizeof(acc));
	for(int set=0; set<2; set++){
		for(int i=0; i<n; i++){
			acc[i+n*set]+=x[i+n*set];//soma ele
			for(int j=0; j<adj[i].size(); j++){
				int v = adj[i][j];
				acc[i+n*set]+= x[v+n*set];//soma os vizinhos
			}
		}
	}

	for(int s = 1; s <= 2;s++){
		for( int set = 0; set < 2; ++set ){
			bool marked[n];
			int count_marked = 0;
			for( int i = 0; i < n; ++i ){
				if(feas[i+n*set] == Infeasible)
					marked[i] = false;
				else{
					marked[i]=true;
					count_marked++;
				}
			}

			int winner;
	
			while( count_marked < n ){
				//choose the star node
				winner = -1;
				for( int i = 0; i < n; ++i ){
					if( !marked[i] ){
						if( winner == -1  ){
							winner = i;
						}
						else if(s==1 && x[i+n*set] > x[winner+n*set] ){
							winner = i;
						}else if(s==2 && acc[i+n*set] < acc[winner+n*set])
							winner = i;
					}
				}
			
				marked[winner] = true;
				++count_marked;
				if(set==1 && (s==1&&newx1[winner]==1 || s==2&&newx2[winner]==1)){
					continue;
				}
				if(s==1){
					newx1[winner+n*set] = 1;
					newobj1++;			
				}else{ //s==2
					newx2[winner+n*set] = 1;
					newobj2++;
				}

				for( int i = 0; i < n; ++i ){
					if( graph[i][winner] ){
						if( !marked[i] ){
							marked[i] = true;
							if(s==1){
								newx1[i+set*n] = 0;
							}else{
								newx2[i+set*n] = 0;
							}
							++count_marked;
							marked[winner] = true;
						}
					}
				}
				int temp = 0;
				for( int i = 0; i < n; i++)
					temp+=marked[i];
			}
		}
	}
	
		int *newx;
		int newobj;
		int op=-1;
		if(newobj1 > newobj2){
			newx = newx1;
			newobj = newobj1;
			op=1;
		}else{
			newx = newx2;
			newobj = newobj2;
			op=2;
		}

		if(newobj > (int)(getIncumbentObjValue()+EPS)){
			if(op==1)op1++;
			else op2++;
			int cont=0;
			for(int i=0; i<2*n; i++){
				x[i] = newx[i];
				cont += x[i];
			}
			tot_sol_heur++;
			setSolution( vars, x, newobj );
		}
	x.end();
	feas.end();
	clock_t t2 = times(&buf2);
	tot_time_heur += (intmax_t) (buf2.tms_utime - buf1.tms_utime);
}




int fix_path(vector<int> &vet, int off, vector<int>& res){
	for(int i=0; i<vet.size(); i++){
		if(vet[i]>=off)
			vet[i]-=off;
	}

	int pilha[2*off];
	int top=0;
	int visit[2*off];
	memset(visit,0, sizeof(visit));
	for(int i=0; i<vet.size()-1; i++){
			if(visit[vet[i]]){
			while(pilha[top-1]!=vet[i]){
				visit[pilha[top-1]]=0;
				top--;
			}
		}
		if(pilha[top-1]==vet[i])continue;
		pilha[top++]=vet[i];
		visit[vet[i]]=true;
	}
	if(top>=5 && top%2){	
		for(int i=0; i<top; i++){
			res.push_back(pilha[i]);
		}
		return 1;
	}
	return (0);
}


double djikstra(int de, int para, vector<vector<pair<int, double> > > &vetor, vector<int> &path, int off){
    int i, no, atual = de;
		int n=2*off;
		double dist[n];
		int pai[n];
    for(i=0; i<n; i++){
			dist[i] = 0xFFFFF;
		}
		pai[de]=-1;
		int visitado[n];
    memset(visitado, 0, sizeof(visitado));
    dist[atual] = 0;

    while(atual!=para){

    	visitado[atual] = 1;
   		for(itR it=vetor[atual].begin(); it != vetor[atual].end(); it++){
         	if(!visitado[it->first] && dist[it->first] > dist[atual] + it->second){
            	dist[it->first] = dist[atual] + it->second;	
							pai[it->first] = atual;
					}
			 }
				atual = -1;
        for(i=0; i<n; i++){
            if(!visitado[i] && (atual == -1 || dist[i] < dist[atual]))
                atual = i;
				}
       if(atual==-1){
					puts("RET");
				  return(-1);  
			}
     }
		atual = para;
		while(atual != -1){
				path.push_back(atual);
				atual = pai[atual];
		}
    return dist[para];
}


inline int getHolleCut( IloNumArray& vals, IloNumVarArray& vars, CutMode cutmode, int set, 
						IloCplex::ControlCallbackI::IntegerFeasibilityArray feas, 
						IloRange& cut, int** graph, int* old_winner, vector<vector<int> >& adj_orig, double *val_cut, vector<vector<int> >& res){

	int n = adj_orig.size();
	int off=n;
	vector<vector<pair<int,double> > > adj;
	for(int i=0; i<2*n; i++){
		adj.push_back(vector<pair<int,double> >());//v+ e v-;
	}
	for(int i=0; i<n; i++){
		for(int j=0; j<adj_orig[i].size(); j++){
			int u=i;
			int v = adj_orig[i][j];
			double val = (1 - vals[n*set+u] - vals[n*set+v])/2.;
			adj[u].push_back(make_pair(v+off, val)); //u+ -> v-
			adj[v+off].push_back(make_pair(u, val));//v- -> u+

		}
	}
	
	for(int i=0; i<n; i++){
		vector<int> path;	
		double dist = djikstra(i, i+n, adj, path, off);
		vector<int> fix;

		int ret = fix_path(path, n, fix);
		if(dist>0.5-EPS)continue;
		bool flag=true;
		//verifica se tem cordas
		for(int k=0; k<fix.size() && flag; k++){
			int sum=0;
			for(int w=k+1; w<fix.size() && flag; w++){
				sum += graph[k][w];
			}
			if(sum!=fix.size()-1)
				flag=false;
		}
		if(flag==false){	
			continue;
		}
		if(set==1){
			for(int k=0; k<fix.size(); k++)
				fix[k]+=n;	
		}
		res.push_back(fix);
		
	}
	return 0;

}

inline int getCut( IloNumArray& vals, IloNumVarArray& vars, CutMode cutmode, int set, 
						IloCplex::ControlCallbackI::IntegerFeasibilityArray feas, 
						IloRange& cut, int** graph, int* old_winner, vector<vector<int> >& adj, double *val_cut ){

	int n = vals.getSize()/2;
	
	bool marked[n];
	for( int i = 0; i < n; ++i )
		marked[i] = false;
	
	int winner;
	int count_marked = 0;
	list<int> indices;
	static int cont=0;
	winner=-1;
	for( int i = 0; i < n; ++i ){
		if(feas[i+n*set] == IloCplex::ControlCallbackI::Infeasible){
			marked[i] = false;
			if(old_winner[i+n*set]==0){
				if( winner == -1 ){
					winner=i;	
				}else if( cutmode == CLQ2B && fabs(vals[i+n*set]-0.5) < fabs(vals[winner+n*set]-0.5) ){
					winner = i;
				}else if( cutmode == CLQ2A && vals[i+n*set] > vals[winner+n*set]){
					winner = i;
				}
			}
		}else{	
			marked[i]=true;
			count_marked++;
		}
	}

	if(winner==-1){
		return -1;
	}

	int ultimo=winner;
	old_winner[winner+n*set]=1;
	indices.push_back(winner);
	int k=0;
	while(true){
		winner=-1;
		for(int i=0; i<adj[ultimo].size(); i++){//tentamos colocar o no adj[winner][i]
			int v = adj[ultimo][i];
			if(old_winner[v+n*set])continue;//se ja colocamos ele antes, continue
			list<int>::iterator it = indices.begin();
			for(; it!=indices.end(); it++){//ele precisa ser adjacente a todos
				if(!graph[v][*it])
					break;
			}	
			if(it!=indices.end())//se nao for adjacente a algum, nao serve
				continue;
			if(marked[v])//ja ja foi pego ou e inteiro, nao serve
				continue;//
			if(winner == -1){
				winner = v;
			}
			else if( cutmode == CLQ2B && fabs(vals[v+n*set]-0.5) < fabs(vals[winner+n*set]-0.5) ){
				winner = v;
			}else if( cutmode == CLQ2A && vals[v+n*set] > vals[winner+n*set] ){
				winner = v;
			}
		}
		if(winner==-1)//se nao encontramos ninguem, pare
			break;
		old_winner[winner+n*set]=1;
		indices.push_back(winner);
		ultimo=winner;
	}
	
	list<int>::iterator it = indices.begin();
	double sum = 0;
	while( it != indices.end() ){
		sum += vals[*it+n*set];
		++it;
	}
		
	if(sum > 1+EPS ){
		it = indices.begin();
		while( it != indices.end() ){
			cut.setLinearCoef( vars[*it+n*set], 1 );
			++it;
		}
		*val_cut = sum-1;
		return 1;
	}
	return 0;
}


bool comp_cuts (pair<IloRange, double>  p1,pair<IloRange, double> p2) { 
	return p1.second > p2.second;
	
}

ILOUSERCUTCALLBACK5( CtCallback, IloNumVarArray, vars, int**, graph, int, num_cuts, int , max_deep, vector<vector<int> > &, adj ) {
	if( first_relaxation_value == -1 ){
		first_relaxation_value = getBestObjValue();
		elapsed_time_at_first_node = (double)( clock() - start )/(double)CLOCKS_PER_SEC;
	}
	tms buf1, buf2;
	clock_t t1 = times(&buf1);
	if(cortados[current_deep] >2)return;
	if(current_deep > max_deep)
		return;

	IloNumArray vals(getEnv());
	getValues(vals, vars);
	IntegerFeasibilityArray feas( getEnv() );
	getFeasibilities( feas, vars );
	int old_win[vals.getSize()];
	memset(old_win, 0, sizeof(old_win));
	vector<pair<IloRange, double> > vet_cuts;
	vector<vector<int> > odd;
	for(int n=0;  n<TRY_CUTS_MULT*num_cuts; n++){
			IloRange cut = IloRange(getEnv(), 0, 1);
			for( int i = 0; i < 2; i++){
				double val_cut=-1;				
				int ret1 = getCut( vals, vars, CLQ2B, i, feas, cut, graph, old_win, adj, &val_cut );
				tot_cut_pass++;
				if (ret1==1){
					vet_cuts.push_back(make_pair(cut, val_cut));	
					cut = IloRange( getEnv(), 0, 1 );
					cut_deep[current_deep]++;
					cut_pass[n]++;
					tot_cuts++;
				}
				int ret2 =  getCut( vals, vars, CLQ2A, i, feas, cut, graph, old_win, adj, &val_cut ) ;
				tot_cut_pass++;
				if(ret2==1){
					vet_cuts.push_back(make_pair(cut, val_cut));
					cut = IloRange(getEnv(), 0, 1 );
					cut_deep[current_deep]++;
					cut_pass[n]++;
					tot_cuts++;

				}if(ret1==-1 && ret2==-1){ //se nao encotrar algum corte, pare
					i=2;
					n=TRY_CUTS_MULT*num_cuts;
				}
		}
		cut.end();
	
	}

	if(sort_cuts)
		sort(vet_cuts.begin(), vet_cuts.end(), comp_cuts); //ordena pelo maior corte
	for(int i=0; i<num_cuts && i<vet_cuts.size(); i++){
		add(vet_cuts[i].first);
		vet_cuts[i].first.end();
		++user_cuts_applied;
	}
	feas.end();
	vals.end();

	clock_t t2 = times(&buf2);
	tot_time_cut += (intmax_t) (buf2.tms_utime - buf1.tms_utime);
}


void BNC::buildModelNF(){
	env = new IloEnv;
	model = new IloModel(*env);
	variables = new IloNumVarArray(*env);
	constraints = new IloRangeArray(*env);
	
	//create variables
	for( int i = 0; i < n; ++i ){
		variables->add( IloIntVar( *env, 0, 1 ) );
		variables->add( IloIntVar( *env, 0, 1 ) );
	}
	

	for( int i = 0, k = 0; i < n; ++i ){
		for( int j = i; j < n; ++j ){
			if( graph[i][j] ){
				IloRange newconstraintA( *env, 0, 1 );
				IloRange newconstraintB( *env, 0, 1 );
				
				newconstraintA.setLinearCoef( (*variables)[i], 1 );
				newconstraintA.setLinearCoef( (*variables)[j], 1 );
				
				newconstraintB.setLinearCoef( (*variables)[n+i], 1 );
				newconstraintB.setLinearCoef( (*variables)[n+j], 1 );
				
				constraints->add( newconstraintA );
				constraints->add( newconstraintB );
				++k;
			}
		}
	}
	
	for( int i = 0; i < n; ++i ){
		IloRange newconstraintAB( *env, 0, 1 );
		newconstraintAB.setLinearCoef( (*variables)[i], 1 );
		newconstraintAB.setLinearCoef( (*variables)[n+i], 1 );
		constraints->add( newconstraintAB );
	}
		
	//objective function
	IloObjective obj = IloMaximize(*env);
	
	//objective
	for( int i = 0 ; i < n; i++ ){
		obj.setLinearCoef((*variables)[i], 1 );
		obj.setLinearCoef((*variables)[n+i], 1 );
	}
	
	model->add( *constraints );
	model->add( obj );
	
	cplex = new IloCplex(*model);
	
	configureCPLEX();
	
	//write model in file cplexmodel.lp
	//cplex->exportModel("cplexmodel.lp");
}

void BNC::buildModelCF(){

	env = new IloEnv;
	model = new IloModel(*env);
	variables = new IloNumVarArray(*env);
	constraints = new IloRangeArray(*env);
	
	list< list<int> > cliques;
	
	int count_chose = 0;
	
	bool chose_edge[n][n];
	for( int i = 0; i < n; ++i )
		for( int j = 0; j < n; ++j )
			chose_edge[i][j] = false;
	
	while( count_chose < m ){
		list<int> current_clique;
		
		//choose a initial node
		for( int i = 0; i < n; ++i ){
			for( int j = 0; j < n; ++j ){
				if( graph[i][j] ){
					if( !chose_edge[i][j] ){
						chose_edge[i][j] = chose_edge[j][i] = true;
						++count_chose;
						current_clique.push_back(i);
						current_clique.push_back(j);
						goto done;
					}
				}
			}
		}
		done:
		//build a clique
		int i = current_clique.front();
		for( int j = 0; j < n; ++j ){
			if( graph[i][j] ){
					bool add_node = true;
					list<int>::iterator it = current_clique.begin();
					while( it != current_clique.end() ){
						if(!graph[*it][j] ){
							add_node = false;
							break;
						}
						++it;
					}
					
					if(add_node){
						list<int>::iterator it = current_clique.begin();
						while(it != current_clique.end() ){
							if(!chose_edge[*it][j] ){
								++count_chose;
								chose_edge[*it][j] = chose_edge[j][*it] = true;
							}
							++it;
						}
						current_clique.push_back(j);
					}
				}
		}
		
		cliques.push_back(current_clique);
	}
	
	//create variables
	for( int i = 0; i < n; ++i ){
		variables->add( IloIntVar( *env, 0, 1 ) );
		variables->add( IloIntVar( *env, 0, 1 ) );
	}
	
	list< list<int> >::iterator it1 = cliques.begin();
	while( it1 !=  cliques.end() ){
		list<int>::iterator it2 = it1->begin();
		IloRange newconstraintA( *env, 0, 1 );
		IloRange newconstraintB( *env, 0, 1 );
		while( it2 != it1->end() ){
			newconstraintA.setLinearCoef( (*variables)[*it2], 1 );
			newconstraintB.setLinearCoef( (*variables)[n+*it2], 1 );
			++it2;
		}
		constraints->add( newconstraintA );
		constraints->add( newconstraintB );
		++it1;
	}

	for( int i = 0; i < n; ++i ){
		IloRange newconstraintAB( *env, 0, 1 );
		newconstraintAB.setLinearCoef( (*variables)[i], 1 );
		newconstraintAB.setLinearCoef( (*variables)[n+i], 1);
		constraints->add( newconstraintAB );
	}
		
	//objective function
	IloObjective obj = IloMaximize(*env);
	
	//objective
	for( int i = 0 ; i < n; i++ ){
		obj.setLinearCoef((*variables)[i], 1 );
		obj.setLinearCoef((*variables)[n+i], 1 );
	}
	
	model->add( *constraints );
	model->add( obj );
	
	cplex = new IloCplex(*model);
	
	configureCPLEX();
	
	//write model in file cplexmodel.lp
	//cplex->exportModel("cplexmodel.lp");
}

void BNC::solve(){
	start = clock();
	if( !strcmp( mod, "FN" ) ){
		solveFNBB();
	}
	else if( !strcmp( mod, "CLQBB" ) ){
		solveCLQBB();
	}
	else if( !strcmp( mod, "CLQBC" ) ){
		solveCLQBC();
	}
	else if( !strcmp( mod, "FNBC" ) ){
		solveFNBC();
	}
	else{
		cout << "Error in file bnc.cpp, function solve: Undefined model" << endl;
		exit(-1);
	}

	end = clock();
	total_elapsed_time = (double)( end - start )/(double)CLOCKS_PER_SEC;

	//printresult adicionado por igor
	printResult();
}

//implementation of the solver by natural formulation + b&b
void BNC::solveFNBB(){
	
	buildModelNF();
	try{
		if( !cplex->solve() ){
			env->error() << "Failed to optimize LP" << endl;
			throw(-1);
		}
	}catch (IloException &e){
			env->error() << e.getMessage();
	}
}

//implementation of the solver by CLQ model + b&b
void BNC::solveCLQBB(){
	
	buildModelCF();
	try{
		if( !cplex->solve() ){
			env->error() << "Failed to optimize LP" << endl;
			throw(-1);
		}
	}catch (IloException &e){
			env->error() << e.getMessage();
	}
}

void BNC::solveFNBC(){
	
	buildModelNF();
	cplex->use( CtCallback(*env, *variables, graph, n_cortes, max_deep, adj ) );
	try{
		if( !cplex->solve() ){
			env->error() << "Failed to optimize LP" << endl;
			throw(-1);
		}
	}catch (IloException &e){
			env->error() << e.getMessage();
	}
}

//implementation of the solver by CLQ model + b&c
void BNC::solveCLQBC(){
	
	buildModelCF();
	
	cplex->use( CtCallback(*env, *variables, graph, n_cortes, max_deep, adj ) );
	try{
		if( !cplex->solve() ){
			env->error() << "Failed to optimize LP" << endl;
			throw(-1);
		}
	}catch (IloException &e){
		env->error() << e.getMessage();
	}
}

void BNC::configureCPLEX(){

	op1=op2=0;

	memset(cut_pass, 0, sizeof(cut_pass));
	memset(cut_deep, 0, sizeof(cut_deep));
	memset(cortados, 0, sizeof(cortados));
	//Controls the frequency of node logging when the MIP display paramete
	 cplex->setParam(IloCplex::MIPDisplay, 3);

	//disable output
	cplex->setOut(env->getNullStream());
		
	cplex->setParam( IloCplex::ClockType, 1);//1:CPU time - 2:physical time

	//define a time limit execution
	cplex->setParam( IloCplex::TiLim, time_limit );
	//disable presolve
	cplex->setParam( IloCplex::PreInd, false );
	
	//assure linear mappings between the presolved and original models
	cplex->setParam( IloCplex::PreLinear, 0 );
	
	//Turn on traditional search for use with control callback
	cplex->setParam( IloCplex::MIPSearch, IloCplex::Traditional);
	
	
	//Decides how often to apply the periodic heuristic. Setting the value to -1 turns off the periodic heuristic
	cplex->setParam( IloCplex::HeurFreq, -1 );

	
	//CPX_PARAM_MIPCBREDLP equivalent is not availible in c++ api
	//cpx_ret = CPXsetintparam (env, CPX_PARAM_MIPCBREDLP, CPX_OFF);
	
	/* impressao para conferencia */
	if (primal_heuristic) {
		//cout << "*** Primal Heuristic is going to be used." << endl;
		cplex->use(Rounddown(*env, *variables, graph, adj));
	}
	//Decides whether or not Gomory fractional cuts should be generated for the problem: -1 disables cuts	
	cplex->setParam( IloCplex::FracCuts, -1 );

	//disable cplex cutting separation
	cplex->setParam( IloCplex::CutsFactor, 1);


	//Controls whether CPLEX applies a local branching heuristic to try to improve new incumbents found during a MIP search
	cplex->setParam( IloCplex::LBHeur, false );

	//Set the upper limit on the number of cutting plane passes CPLEX performs when solving the root node of a MIP model
	printf("N cortes %d\n", n_cortes);
	printf("MaxDeep %d\n", max_deep);
	


	//actives the node callback MySelect
	cplex->use( MySelect( *env, &current_deep ) );
}

//http://eaton.math.rpi.edu/cplex90html/usrcplex/goals2.html cuts per time



void BNC::printResult(){
	//*
	IloNumArray vals(*env);
	env->out() << "Solution status = " << cplex->getStatus() << endl;
	env->out() << "Solution value  = " << cplex->getObjValue() << endl;
	env->out() << "GAP             = " << cplex->getMIPRelativeGap()*100 << "%"<< endl;
	env->out() << "ITERACOES       = " << cplex->getNiterations() << endl;
	env->out() << "NUMERO NODOS       = " << cplex->getNnodes() << endl;
	cout << "Heuristica 1 : " <<op1 << endl;
	cout << "Heuristica 2 : " <<op2 << endl;
	cplex->getValues(vals, *variables);
	cout << "A = [ ";
	for( int i = 0; i < n; ++i )
		cout << vals[i] << " ";
	cout << "]" << endl;
	cout << "B = [ ";
	for( int i = 0; i < n; ++i )
		cout << vals[n+i] << " ";
	cout << "]" << endl;
	puts("CONT PASS");
	for(int i=0; i<50; i++)
		printf("%d ", cut_pass[i]);
	puts("\n");
	puts("CONT DEEP");
	for(int i=0; i<70; i++)
		printf("%d ", cut_deep[i]);
	puts("\n");
	printf("TOT_TIME_CUTS %.3lf\n", tot_time_cut/100.);
	printf("TOT_CUTS %d\n", tot_cuts);
	
	printf("\n");
	printf("TOT_TIME_HEUR %.3lf\n", tot_time_heur/100.);
	printf("TOT_SOL_HEUR %d\n", tot_sol_heur);
	//*/
	
	ofstream out;
	out.open( out_file_sol.c_str() );
	//out.open( "xeta1" );
	if( !out.is_open() ){
		cout << "Error in bnc.cpp, function printResult: Could not open file " << out_file_sol << endl;
		exit(-1);
	}
	
	//SAIDA ARQUIVO .sol
	
	//A primeira linha deve conter os parâmetros de entrada passados para o programa 
	out << mod << " " << time_limit << " " << primal_heuristic << " " << input_file << endl;
	
	//A segunda linha deve conter os limitantes primal e dual (arredondados para o inteiro mais próximo) encontrados 
	out << cplex->getObjValue() << " " << (int)(cplex->getBestObjValue()+EPS) << endl;
	
	int verticesQ1 = 0;
	int verticesQ2 = 0;
	for( int i = 0; i < n; ++i ){
		if(vals[i])
			verticesQ1++;
		
		if(vals[n+i])
			verticesQ2++;
	}
	//A quarta linha deve conter a quantidade de vértices nas partições I1 e I2 pertencentes à melhor solução primal
	out << verticesQ1 << " " << verticesQ2 << endl;
	
	//Nas q1 linhas seguintes devem ser impressos os números inteiros correspondentes aos vértices pertencentes à partição I1 
	for( int i = 0; i < n; ++i )
		if(vals[i])
			out << i+1 << endl;
			
	//Nas q2 linhas seguintes, os números inteiros correspondentes aos vértices pertencentes à partição I2;
	for( int i = 0; i < n; ++i )
		if(vals[n+i])
			out << i+1 << endl;
	
	out.close();	
	
	out.open( out_file_est.c_str() );
	//out.open( "xeta2" );
	if( !out.is_open() ){
		cout << "Error in bnc.cpp, function printResult: Could not open file " << out_file_est << endl;
		exit(-1);
	}
	out.setf(ios::fixed,ios::floatfield);
	
	
	//SAIDA ARQUIVO .est
	
	//A primeira linha deve conter os parâmetros de entrada passados para o programa 
	out << mod << " " << time_limit << " " << primal_heuristic << " " << input_file << endl;
	
	//um double com o melhor limitante primal, 
	out.precision(6);
	out << cplex->getObjValue() << endl;
	
	//um double com o melhor limitante dual, 
	out << cplex->getBestObjValue()+EPS << endl;
	
	//um inteiro com o tempo total de execução (em segundos), 
	out.precision(0);
	out << (int)total_elapsed_time << endl;
	
	//um double com o valor da função objetivo da primeira relaxação, 
	out.precision(6);
	out << first_relaxation_value << endl;
	
	//um inteiro com o tempo utilizado na primeira relaxação (em segundos), 
	out.precision(0);
	out << elapsed_time_at_first_node << endl;
	
	//um inteiro com o total de nós explorados, 
	out << cplex->getNnodes() << endl;
	
	//um inteiro com o nó no qual foi encontrada a melhor solução primal
	out << cplex->getIncumbentNode() << endl;
	
	//o número de cortes inseridos pelo algoritmo de branch-and-cut (zero no caso de ser um branch-and-bound). 
	out << user_cuts_applied << endl;
	
	out.close();
}
