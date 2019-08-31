//Copyright 2018 Pandey A.
//Strict dependency on g++ 2017 standard
//Heuristic driven solution to SAT solving (NP)
#include<iostream>
#include<cstdio>
#include<cstdlib>
#include<fstream>
#include<vector>
#include<cstring>
#include<ctime>
#include<thread>
#include<chrono>
#include<algorithm>
using namespace std;
//By default satisfiability value is 0 (false)
int sat=0;
int counter=0;
//This function will print the Distinct elements of the track array
void printDistinct(int arr[], int n){
	for (int i=0; i<n; i++){
		int j;
		for (j=0; j<i; j++) if (arr[i] == arr[j]) break;
		if (i == j) cout << arr[i] << " ";
	}
}
/*solve function recursively solves the problem
using semantic tableaux but instead stops the propogation
once a contradiction is reached. If p is included ever in
the track then ~p is never included. The check is O(1).*/
int solve(vector<int> query[], int var, int clauses, int track[], int start,bool visited[]){
	if(sat==1) return 0;
	if(counter%100000==0) system("clear");
	if(counter%10000==0) cout<<start<<"-"<<flush;
	counter++;
	//if(counter%100000==0) cout<<start<<"----";
	//No need to continue if satisfiability is reached
	//If a leave is reached it performs a sanity check and outputs the track
	if(start==clauses){
		//for(int i=1;i<=var;i++) if(track[i]==1&&track[i+var]==1) return 0;
		sat=1;
		cout<<"SAT"<<endl;
		sort(track,track+clauses,[](int i, int j){return abs(i)<abs(j);});
		printDistinct(track,clauses);
		return 0;
	}
	int flag=0;
	for(std::vector<int>::iterator it=query[start].begin();it!=query[start].end();it++){
		if((*it)>0&&visited[*it]==1){flag=1; track[start]=*it; break;}
		if((*it)<0&&visited[var+abs(*it)]==1){flag=1; track[start]=*it; break;}
	}
	if(flag){
		solve(query,var,clauses,track,start+1,visited);
		return 0;
	}
	//Iterate through the vector and include the value in track
	for(std::vector<int>::iterator it=query[start].begin();it!=query[start].end();it++){
		track[start]=*it;
		//check if the negation of a preposition is not present
		if(track[start]>0&&visited[track[start]]==1){
			solve(query,var,clauses,track,start+1,visited);
			if(sat==1) return 0;
		}
		else if(track[start]<0&&visited[var+abs(track[start])]==1){
			solve(query,var,clauses,track,start+1,visited);
			if(sat==1) return 0;
		}
		else if(track[start]>0&&visited[var+track[start]]==0){
			visited[track[start]]=1;
			solve(query,var,clauses,track,start+1,visited);
			if(sat==1) return 0;
			visited[track[start]]=0;
		}
		else if(track[start]<0&&visited[abs(*it)]==0){
			visited[var+abs(track[start])]=1;
			solve(query,var,clauses,track,start+1,visited);
			if(sat==1) return 0;
			visited[var+abs(track[start])]=0;
		}
	}
	return 0;
}
int main(){
	//Clock start
	clock_t start=clock();
	//Opens the file from which input is read
	FILE* fp=fopen("sat.txt","r");

	//Declaration of variables
	//var=Number of variables clauses=Number of Clauses
	int var=0,clauses=0;
	fscanf(fp,"p cnf %d %d",&var,&clauses);
	//Checks if a preposition is present in a track or not
	bool visited[2*(var)+1];
	//Stores the query
	vector<int> query[clauses];
	//Count occurence of variables (positive and negative counted the same)
	int occur[var+1];
	//Track will store all prepositions encountered in the path of a semantic tableaux
	int track[clauses];
	int temp=0;

	//initializing
	for(int i=0;i<2*(var)+1;i++) visited[i]=0;
	//for(int i=var+1;i<2*(var)+1;i++) visited[i]=1;
	for(int i=0; i<var+1; i++) occur[i]=0;
	for(int i=0;i<clauses;i++) track[i]=0;

	//Query input
	for(int i=0; i<clauses;i++){
		while(1){
			fscanf(fp,"%d",&temp);
			if(temp==0) break;
			query[i].push_back(temp);
			occur[abs(temp)]++;
		}
	}
	//Sort each query according to occurence(Largest to Least)
	for(int i=0;i<clauses;i++){
		sort(query[i].begin(),query[i].end(),[&occur](int i, int j) { return occur[abs(i)] > occur[abs(j)];});
	}
	//Sort all queries according to size(Least to Largest)
	sort(query,query+clauses,[](vector<int> i, vector<int> j){ return i.size()<j.size();});
	//Call solve function
	solve(query,var,clauses,track,0,visited);

	//if not satisfiable
	if(sat==0) cout<<"UNSAT";
	//for(int i=1;i<=var;i++) cout<<visited[i]<<","<<visited[var+i]<<endl;
	fclose(fp);
	//Clock over
	printf("\n---------%f seconds--------\n",(double)(clock()-start)/CLOCKS_PER_SEC);
	cout<<counter;
	return 0;
}
