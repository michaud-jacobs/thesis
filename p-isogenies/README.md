This folder contains Magma code to support the computations in Chapter 5 of my thesis (Elliptic curves with p-isogenies over quadratic fields). All code runs on Magma V2.27-7 (and hopefully on later versions too). All timings refer to computations running on a 2200 MHz AMD Opteron.

This folder contains the following files (more description is contained within each file):

- [constant_sig_general.m](constant_sig_general.m) computes bad constant isogeny signature primes for a given class group exponent.
- [constant_sig_specific.m](constant_sig_specific.m) computes bad constant isogeny signature primes for a given quadratic field.
- [formal_imm_mp.m](formal_imm_mp.m) verifies the ranks of certain formal immersion matrices.
- [non_constant_sig.m](non_constant_sig.m) computes bad non-constant isogeny signature primes for a given quadratic field.
- [small_isog.m](small_isog.m) uses modular curves to check for small degree isogenies.
- [small_isog_output.txt](small_isog_output.txt) contains the output of the `small_isog.m` file.
