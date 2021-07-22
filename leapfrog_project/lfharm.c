/*
 * LFHARM.C: program to integrate harmonic oscillator using leapfrog.
 */

#include <math.h>

/*
 * FORCE: compute force for harmonic oscillator, unity mass.
 */

float force(float *x)
{
  return -1.0f * *x;
}

/*
 * LFSTEP: one step of integration.
 */

void lfstep(float *x, float *v, float h)
{
  float a;

  a = force(x);
  *x = *x + h * *v + 0.5f * ((h * h) * force(x));		/* position step */
  *v = *v + 0.5f * (h * (force(x) + a));		/* velocity step */
}

void integrate(float *x, float *v) {
    int n, max_step, nstep;
    float t, h;

    /* initial conditions */
    *x = 1.0f; *v = 0.0f; t = 0.0f;

    /* integration parameters */
    max_step = 100;				/* number of integration steps */
    h = 1.0f / 32.0f;				/* timestep */

    /* integration loop */
    for (n = 0; n < max_step; n++)
    {
	   lfstep(x, v, h);			/* integration step */
	   t = t + h;
    }

}
  
int main(void)
{
    float x, v;
    integrate (&x, &v);
    return 0;
}

