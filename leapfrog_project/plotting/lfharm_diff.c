/*
 * Purpose: this file produces two txt files. 
 * file1 : random inputs used for leapfrog integration, 
 * file2 : absolute error (first x then v) between sngl and dbl 
 *         precision on random inputs. 
 *
 * Author: Ariel Kellison, December 2021
 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* generate a random floating point number from min to max */
double randfrom(double min, double max)
{
    double range = (max - min);
    double div = RAND_MAX / range;
    return min + (rand() / div);
}

/* one step in single prec */
void lfstep32(float **x, float **v, float h, int size)
{
	float a;

	for (int n = 0; n < size; n++){
		a = -1.0f * (*x)[n];
	  	(*x)[n] = (*x)[n] + h * (*v)[n] + 0.5f * (h * h * -1.0f * (*x)[n]);		/* position step */
  		(*v)[n] = (*v)[n] + 0.5f * (h * -1.0f * (*x)[n] + a);		/* velocity step */
	}
}

/* one step in double prec */
void lfstep64(double **x, double **v, double h, int size)
{

	double a;

	for (int n = 0; n < size; n++){
		a = -1.0 * (*x)[n];
  		(*x)[n] = (*x)[n] + h * (*v)[n] + 0.5 * (h * h * -1.0 * (*x)[n]);		/* position step */
  		(*v)[n] = (*v)[n] + 0.5 * (h * -1.0 * (*x)[n] + a);		/* velocity step */
	}
}

/* main */
int main(int argc, char *argv[]){
	
	if (argc <= 3 ){
    		printf("Takes two arguments: number of inputs, id for filename\n");
    		return 0;
	}
	
	int max  = atoi(argv[1]);
	double hd = 1.0/32.0;
	float hf  = (float) hd;
	char filename1[25]= "lf_in_data_";
	char filename2[25]= "lf_out_data_";

	strncat(filename1, argv[2], 5);
	strncat(filename2, argv[2], 5);
	strncat(filename1, ".txt", 5);
	strncat(filename2, ".txt", 5);

	FILE *lf_in_data;
	FILE *lf_out_data;

	double *xdrands = calloc(max, sizeof(double));
	float *xfrands  = calloc(max, sizeof(float));
	double *vdrands = calloc(max, sizeof(double));
	float *vfrands  = calloc(max, sizeof(float));

	for (int n = 0; n < max; n++){
		xfrands[n] = randfrom(-1.0, 1.0);
		xdrands[n] = xfrands[n];
		vfrands[n] = randfrom(-1.0, 1.0);
		vdrands[n] = vfrands[n];
	}

	lf_in_data = fopen(filename1, "w");
	for (int i = 0; i < max; i++) {
			fprintf(lf_in_data,"%.17g\n", xdrands[i]);
	}
	for (int i = 0; i < max; i++) {
			fprintf(lf_in_data,"%.17g\n", vdrands[i]);
	}
	fclose(lf_in_data);

	lfstep64(&xdrands,&vdrands,hd,max);
	lfstep32(&xfrands,&vfrands,hf,max);

	double *abs_err_x  = calloc(max, sizeof(double));
	double *abs_err_v  = calloc(max, sizeof(double));

	for (int i = 0; i < max; i++) {
			abs_err_x[i] = fabs(xdrands[i] - xfrands[i]);
			abs_err_v[i] = fabs(vdrands[i] - vfrands[i]);
	}

	lf_out_data = fopen(filename2, "w");
	for (int i = 0; i < max; i++) {
	    fprintf(lf_out_data, "%.17g\n", abs_err_x[i]);
	}
	for (int i = 0; i < max; i++) {
			fprintf(lf_out_data, "%.17g\n", abs_err_v[i]);
	}
	fclose(lf_out_data);

	free(xfrands);
	free(xdrands);
	free(vfrands);
	free(vdrands);
	free(abs_err_x);
	free(abs_err_v);

  return 0 ;
}

