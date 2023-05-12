# quad-cartan
This folder contains Magma code to support the computations in Chapter 3 of my thesis (Quadratic points on non-split Cartan modular curves). All code runs on Magma V2.27-7 (and hopefully on later versions too). All timings refer to computations running on a 2200 MHz AMD Opteron.

This folder contains the following files (more description is contained within each file):

- [Xns11.m](Xns11.m) contains some calculations for the curve X_ns(11).
- [eqn_data.m](eqn_data.m) contains equations for models and maps.
- [model.m](model.m) obtains a new model for X_ns(13).
- [saturation.m](saturation.m) carries out the saturation tests.
- [saturation_output.txt](saturation.m) contains the output of the `saturation.m` file.
- [sieve.m](saturation.m) carries out the sieving step.
- [sieve_output.txt](saturation.m) contains the output of the `sieve.m` file.

