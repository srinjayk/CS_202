#include <iostream>
#include <cstdlib>
using namespace std;



int main()
{

	int n;
	int count;
	int i,j,k,l,q;
	cin >>n;
	 scanf("\n");
    int h;
    int d;
	for (i = 0; i < n; i++) {
		int m;
		cin >>m;
		int arr[m];
		count=0;
		scanf("\n");
		for (j = 0; j < m; j++) {
			cin>>arr[j];
			//cout<<arr[j]<<" ";
			q=arr[j]+arr[j-1];
			//cout<<q<<" ";

		}
		cout<<q<<" ";

		d=arr[m-1]+arr[m];
		//cout<<d<<" ";

		int b=((m)*(m-1))/2;
		for (k = 0; k <m-1; k++) {
			for (l = k+1; l < m; l++) {
			    int h=arr[k]+arr[l];
			    int u=arr[m]+arr[m-1];
			    cout<<h<<" ";

				if(q==h){
				    count++;
				    //cout<<h<<" ";
				}
			}
		}
		scanf("\n");
		float prob;
		prob=((float)count)/b;
		printf("%f\n",prob);
	}


	return 0;
}
