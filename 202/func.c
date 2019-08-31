//function to check if array is State

char arr[n];
for (int i = 0; i < n; i++)
{
  arr[i]='Y';
}

int arr1[n];
for(i=0;i<n;i++)
{
  int h=arr1[i];
  if((arr[h]=='N')&&(arr1[i]<0))
    break;
  else if((arr[h]=='Y')&&(arr1[i]>0))
    break;
  else{
    if (arr1[i]>0)
      arr[h]='Y';
    else
      arr[-h]='N';
  }
}
