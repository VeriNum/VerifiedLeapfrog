/*
 * LEAPINT_HARM.C: program to integrate harmonic oscillator using leapfrog.
 */

#include <math.h>
#include <stdio.h>

/*
 * FORCE: compute force for harmonic oscillator, unity mass.
 */

float force(float *x)
{
  return -1.0 * *x;				      /* use linear force law     */
}

/*
 * LEAPSTEP: one step of integration
 */

void leapstep(float *x, float *v, float h)
{
  float a;

  a = force(x);
	*x = *x + h * *v + 0.5 * h * h * force(x);		/* position step */
	*v = *v + 0.5 * h * (force(x) + a);		/* velocity step */
}

void main()
{
    int n, max_step, nstep;
    float x, v;
    float t, h;

    /* initial conditions */
    x = 1.0; v = 0.0; t = 0.0;

    /* integration parameters */
    max_step = 100;				/* number of steps to take  */
    h = 1.0 / 32.0;				/* timestep for integration */

    /* integration loop */
    for (n = 0; n < max_step; n++)
    {
	   leapstep(&x, &v, h);			/* integration step */
	   t = t + h; /* update time */
    }
    printf("x: %f\n",x);
    printf("v: %f",v);

}

