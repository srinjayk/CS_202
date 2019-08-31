#include<stdio.h>

void check(int* arr, int m,int n) {
  int i,j;
  for(i=0;i<n;i++)
  {
    for(j=0;j<m;j++)
    {
      
    }
  }
}

int main()
{
  int m,n;
  FILE *in_file  = fopen("input.txt", "r");
  fscanf(in_file,"p cnf %d %d\n",&m,&n);
  //printf("%d %d\n",m,n );
  int arr[n][m];
  int i,j;
  for(i=0;i<n;i++)
  {
    for(j=0;j<m;j++)
    {
      arr[i][j]=0;
    }
  }

  for(i=0;i<n;i++)
  {
    for(j=0;j<m;j++)
    {

      fscanf(in_file,"%d ",&arr[i][j]);

    }
    fscanf(in_file,"\n");
  }

/*  for(i=0;i<n;i++)
  {
    for(j=0;j<m;j++)
    {
      printf("%d ",arr[i][j]);
    }
    printf("\n");
  }*/
  int arr_mod[m*n];
  for(i=0;i<n;i++)
  {
    for(j=0;j<m;j++)
    {
      arr_mod[i*m+j]=arr[i][j];
    }

  }

  check(arr_mod,m,n);

  /*for(i=0;i<n;i++)
  {
    for(j=0;j<m;j++)
    {
      printf("%d ",arr_mod[i*m+j]);
    }
    printf("\n");
  }*/

  fclose(in_file);
  return 0;
}
