/*
 * LFHARM.C: program to integrate harmonic oscillator using leapfrog.
 */

#include <math.h>

struct state {float p, q;};

/*
 * FORCE: compute force for harmonic oscillator, unity mass.
 */

float force(float q) {
  return -q;
}

/*
 * LFSTEP: one step of integration.
 */

void lfstep(struct state *s, float h) {
  float a;

  a = force(s->q);
  s->q = s->q + h * s->p + (0.5f * (h * h)) * a;	/* position step */
  s->p = s->p + (0.5f * h) * (a + force(s->q));		/* velocity step */
}

void integrate(struct state *s) {
    int n, max_step, nstep;
    float t, h;

    s->q = 1.0f; s->p = 0.0f; t = 0.0f;     /* initial conditions */

    max_step = 1000;	                /* number of integration steps */
    h = 1.0f / 32.0f;			/* timestep */

    /* integration loop */
    for (n = 0; n < max_step; n++) {
	   lfstep(s, h);
	   t = t + h;
    }
}
  
int main(void) {
    struct state s;
    integrate (&s);
    return 0;
}
