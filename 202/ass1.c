#include<stdio.h>

int main()
{
  int m,n;
  int s,t,k,l;
//  FILE *in_file  = fopen("input.txt", "r");
  scanf("p cnf %d %d\n",&m,&n);
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
      scanf("%d ",&arr[i][j]);

    }
    scanf("\n");
  }

/*  for(i=0;i<n;i++)
  {
    //int o=0;
    for(j=0;j<m;j++)
    {
      printf("%d ",arr[i][j]);
    }
    printf("\n");
  }*/

  for(i=0;i<n;i++)
  {
    for(j=0;j<m;j++)
    {
      int arr1[n][m];
      int h=arr[i][j];
      if (h==0)
      {
        break;
      }
      for(k=0;k<n;k++)
      {
        for(l=0;l<m;l++)
        {
          arr1[0][0]=0;
          if (arr[k][l]*h==h*h)
          {
            arr1[k][l]=1;
          }
          else if((arr[k][l]*h==(-h)*h)||(arr[k][l]==0))
          {
            arr1[k][l]=-1;
          }
          else
          {
            arr1[k][l]=0;
          }
        }
      }

      /*for(k=0;k<n;k++)
      {
        for(l=0;l<m;l++)
        {
          printf("%d ",arr1[k][l]);
        }
        printf("\n");
      }*/

      for(k=0;k<n;k++)
      {
        int o=0;
        for(l=0;l<m;l++)
        {
          if (arr[k][l]!=-1)
          {
            o=1;
            break;
          }
        }
        if (o==1)
        {
          printf("SAT");
          return 0;
        }
      }


    }
  }
  printf("UNSAT\n");

  return 0;
}
