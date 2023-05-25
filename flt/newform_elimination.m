// Magma code to support the computations in my PhD thesis.

// The code in this file carries out the main elimination of newform step.

// The output is in the file "newform_elimination_output.txt", available at
// https://github.com/michaud-jacobs/thesis/blob/main/flt/newform_elimination_output.txt

// The code uses the functions "hecke_elim" and "decomp_elim" from the file "newform_elimination_functions.m" available at:
// https://github.com/michaud-jacobs/thesis/blob/main/flt/levels_function.m

load "newform_elimination_functions.m";

////////////////////////////////////////////

// We carry out the elimination step:

too_big_d := [39, 70, 78, 95]; // Dimensions too large for computations (some dimension > 10000)

// Note that the computations for d = 34, 42, 55, 66, 91 require a lot of memory (some dimension > 3000)
// Especially d = 55, 66 (some dimension > 7000)

// We now eliminate newforms
// We start by only using hecke_elim

// We include data for 1 < d < 25 to compare with Freitas and Siksek's paper
// The output is available in the "newform_elimination_output.txt" file

for d in [d : d in [2..100] | IsSquarefree(d) and d notin (too_big_d)] do
    print "Considering d = ", d;
    N_ps, K := Np_possibilities(d);
    for Np in N_ps do
        print "Considering level Np with factorisation:", Factorisation(Np);
        elim := hecke_elim(Np,K);
        print "+++++++++++++++++++++++++++++++++++++++++++++++++";
    end for;
    print "====================================================================";
    print "====================================================================";
    print "====================================================================";
end for;

// We now use decomp_elim to eliminate the following triples (d,p,Np):
// (d,p,Np) = (67,19,N_ps[2]) and (d,p) = (55,17,N_ps[4])
// We note we could also eliminate these two pairs (d,p)
// using the method of regular primes (as used at the end of the chapter in the case d = 57 and p = 19) as they are d-regular.

d := 67;
N_ps, K := Np_possibilities(d);
Np := N_ps[2];
bad_primes := decomp_elim(Np,K,100); // Ouput: [ 2, 3, 5, 7, 11 ]
assert 19 notin bad_primes;

d := 55;
N_ps, K := Np_possibilities(d);
Np := N_ps[4];
bad_primes := decomp_elim(Np,K,100); // Output: [ 2, 3 ]
assert 17 notin bad_primes;
