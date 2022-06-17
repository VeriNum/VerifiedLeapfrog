#include <math.h>
#include <stdio.h>
#include <stdlib.h>

double sqr (double x) { return x*x; }

const float h = 1.0f / 32.0f;			/* timestep */

float integrate(float p, float q, int N) {
  int n;
    for (n = 0; n < N; n++) {
      float a = -q;
      q = q + h * p + (0.5f * (h * h)) * a;
      p = p + (0.5f * h) * (a + -q);
    }
    return q;
}

float closedform(float p, float q, int N) {
  double t=atan2(q,p);
  double r=sqrt(sqr(q)+sqr(p));
  return r*sin(t+h*N);
}

double sigma (double h) {
  double h3 = h*h*h;
  double a = sqrt (h3*h3+64);
  double A = (h3*h3*h3*h+h3*h3*h*a+4*h3*h3+64*h3*h+4*h3*a+32*h*a+256)*sqr(h*h-2);
  return sqrt (A / (2*(h3*h-4*h*h+4)*(sqr(-h3+8*h+a)+16*sqr(h*h-2))));
}

double error_bound(double h, int N) {
  double tau_d = h*h*h;
  double tau_r = 1.399e-7;
  double sigma_h = sigma(h);
  double acc = (tau_d+tau_r)*((pow(sigma_h,N)-1.0)/(sigma_h-1.0));
  fprintf(stderr,"h=%f  N=%d\n", h, N);
  fprintf(stderr,"tau_d=%0.10f  sigma_h=%0.10f  acc=%f\n",
	  tau_d, sigma_h, acc);
  return acc;
}
  
#define HIST 1000

int histogram[HIST];
double worst, worstp, worstq;

int main(int argc, char **argv) {
  int numtries, N; int i, histmax=0;
    if (argc!=3) {fprintf(stderr,"usage: findbad N num_tries\n"); exit(1);}
    N=atoi(argv[1]);
    if (N<0) {fprintf(stderr,"N must be positive\n"); exit(1);}
    numtries=atoi(argv[2]);
    if (numtries<=0) {fprintf(stderr,"num_tries must be positive\n"); exit(1);}

    double bound = error_bound(h,N);
    for (i=0; i<numtries; i++) {
      double p,q,r, pN, err;
      double disc,clos;
      do {p=drand48(); q=drand48(); r=sqr(p)+sqr(q);}
      while (r < 0.8 || r > 1.0);
      disc=integrate(p,q,N);
      clos=closedform(p,q,N);
      err = fabs(disc-clos);
      if (err>worst) {
	worst=err; worstp=p; worstq=q;
	printf("Worst so far: %5.2f%%, p=%f, q=%f %s\n",100.0*err/bound,p,q,
		err>bound?"which is amazing!":"");
        fflush(stdout);
      }
      if (err<bound)
	histogram[(int)(err*HIST/bound)]++;
    }
    for (i=0; i<HIST; i++) if (histogram[i]) histmax=i;
    for (i=0; i<=histmax; i++)
      printf(">= %5.2f%% : %10d\n",(i*bound/HIST)*100.0/bound, histogram[i]);
    return 0;
}
