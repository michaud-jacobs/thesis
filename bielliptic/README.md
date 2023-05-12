This folder contains Magma code to support the computations in Chapter 4 of my thesis (Copmuting points on bielliptic modular curves over fixed quadratic fields). All code runs on Magma V2.27-7 (and hopefully on later versions too). All timings refer to computations running on a 2200 MHz AMD Opteron.

This folder contains the following files (more description is contained within each file):

- [bielliptic_models.m](bielliptic_models.m) provides code for computing suitable models for X_0(N) and checking nonsingularity.
- [bielliptic_sieve.m](bielliptic_sieve.m) contains an implementation of the Mordell–Weil sieve used. It contains code to support the computations in the proof of the main theorem of the chapter as well as for the example computations.
- [bielliptic_sieve_output.txt](bielliptic_sieve_output.txt) contains the output of the `bielliptic_sieve.m` file.
- [local_point_comparison.m](local_point_comparison.m) contains computations that use the local point method.
