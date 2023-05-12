# flt-quad
This folder contains Magma code to support the computations in Chapter 7 of my thesis (Fermat's Last Theorem over real quadratic fields). All code runs on Magma V2.27-7 (and hopefully on later versions too). All timings refer to computations running on a 2200 MHz AMD Opteron.

This folder contains the following files (more description is contained within each file):

- [irreducibility.m](irreducibility.m) carries out the irreducibility checks.
- [levels_function.m](levels_function.m) contains the main function for computing the possible levels N_p for Hilbert newforms.
- [levels.m](levels.m) computes the possible levels N_p for Hilbert newforms.
- [levels_output.txt](levels_output.txt) contains the output of the `levels.m` file.
- [newform_elimination_functions.m](newform_elimination_functions.m) contains functions for eliminating newforms.
- [newform_elimination.m](newform_elimination.m) carries out the newform elimination checks.
- [newform_elimination_output.txt](newform_elimination_output.txt) contains the output of the `newform_elimination.m` file.
- [remaining_cases.m](remaining_cases.m) completes the elimination of newform steps.
- [remaining_cases_output.txt](remaining_cases_output.txt) contains the output of the `remaining_cases.m` file.
