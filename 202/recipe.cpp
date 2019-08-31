#include<iostream>
using namespace std;


int main(){
  int n;
  cin >>n;
  scanf("\n");
  for (int i = 0; i < n; i++) {
    int a,b,c,d,e;
    cin >>a>>b>>c>>d>>e;
    scanf("\n");
    //cout <<a<<b<<c<<d<<e;
    float f,g;
    f=float(abs(c-a))/d;
    g=float(abs(c-b))/e;
    if (f<g) {cout<<"Chef"<<endl;}
    else if(g<f) {cout<<"Kefa"<<endl;}
    else {cout<<"Draw"<<endl;}
  }
  return 0;

}
