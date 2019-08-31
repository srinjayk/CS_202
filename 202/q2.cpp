#include<iostream>
#include<stdio.h>

using namespace std;

int main() {
  int n;
  cin >>n;
  scanf("\n");
  for (int i = 0; i < n; i++) {
    int m;
    cin >>m;
    int arr[m+1];
    arr[0]=0;
    scanf("\n");
    for (int j = 1; j <= m; j++) {
      cin>>arr[j];
    }
    scanf("\n");
    int arr_arr[m+1];
    for (int k = 1; k <= m; k++){
        arr_arr[k]=0;
        int temp=arr[k];
        //cout<<temp<<"   ";
        arr_arr[k]=arr[temp];
    }

    int y=0;
    for (int k = 1; k < m; k++) {
      for (int h = k+1; h < m+1; h++) {
        if((arr[k]!=arr[h])&&(arr_arr[h]==arr_arr[k])){
          std::cout << "Truly Happy" <<endl;
          y=1;
          break;
        }
        if(y==1) break;
      }
      if(y==1) break;
    }
    if(y==0) cout<<"Poor Chef"<<endl;

  }
  return 0;
}
