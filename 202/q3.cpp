#include<iostream>

using namespace std;

int main(){
  int n;
  cin >>n;
  for (int i = 0; i < n; i++) {
    int m;
    cin >>m;
    pair <int,int> num;
    pair <int,int> temp;

    num.first=1;
    num.second=2;
    if(m==1) cout<<1<<" "<<2<<" ";
    if(m==2) cout<<1<<" "<<4<<" ";
    if(m>2){
      for (int j = 3; j <= m; j++) {
        if(j%2){
          temp=num;
          num.first=2*temp.first+1;
          num.second=2*temp.second;
        }
        else{
          temp=num;
          num.first=2*temp.first-1;
          num.second=2*temp.second;
        }
      }
    }
    if(m%2) cout<<odd.first<<" "<<odd.second<<" ";
    else cout<<even.first<<" "<<even.second<<" ";
  }
  return 0;
}
