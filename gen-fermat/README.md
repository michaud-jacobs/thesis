This folder contains Magma code to support the computations in Chapter 8 of my thesis (Generalized Fermat equations of the form x^2 + y^2n = z^p). All code runs on Magma V2.27-7 (and hopefully on later versions too). All timings refer to computations running on a 2200 MHz AMD Opteron.

This folder contains the following files (more description is contained within each file):

- [asymptotic_constants.m](asymptotic_constants.m) computes explicit constants for irreducibility and dimensions of Hilbert cusp forms for signature (2, 2n, 3p).
- [cuspforms_7.m](cuspforms_7.m) verifies the Hilbert cusp form computation for signature (2, 2n, 21).
- [cuspforms_17.m](cuspforms_17.m) verifies the Hilbert cusp form computations for signature (2m, 2l, 17).
- [cuspforms_17_output.txt](cuspforms_17_output.txt) contains the output of the `cuspforms_17.m` file.
- [irreducibility_17.m](irreducibility_17.m) carries out the irreducibility computations for signature (2m, 2l, 17).
