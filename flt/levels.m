// Magma code to support the computations in my PhD thesis.

// The code in this file executes the "Np_possibilities" function
// to compute the possible levels after level-lowering.
// This function is in the "levels_function.m" file, available at
// https://github.com/michaud-jacobs/thesis/blob/main/flt/levels_function.m

// The output is in the file "levels_output.txt", available at
// https://github.com/michaud-jacobs/thesis/blob/main/flt/levels_output.txt

load "levels_function.m";

////////////////////////////////////////////

// We list the possible levels N_p for each d
// We also list the dimensions of the spaces of modular forms and newforms
// See the output file "levels_output.txt".
// We include data for 1 < d < 25 to check against Freitas and Siksek's paper.

for d in [d : d in [2..100] | IsSquarefree(d)] do
    print "Computing the possible levels N_p for d =", d;
    N_ps, K, S, H := Np_possibilities(d); // S is the set of primes above 2 and H are the representatives for Cl(K)/2*Cl(K)
    if #S eq 2 then
        print "2 splits in K and S = {p_1, p_2}";
    else if Norm(S[1]) eq 2 then
             print "2 is ramified in K and S = {p}";
         else print "2 is inert in K and S = {p = 2O}";
         end if;
    end if;
    r := #H;
    print "Cl(K) / Cl(K)^2 has size r =", r;
    if r eq 2 then
        m := H[2];
        m_gens := [K ! gg : gg in Generators(m)];
        printf "The ideal m is generated by %o and %o \n", m_gens[1], m_gens[2];
    else print "The ideal m is generated by 1";
    end if;
    print "Possible levels N_p are:", [Factorisation(np) : np in N_ps];
    for Np in N_ps do
        M := HilbertCuspForms(K, Np);
        NewM:=NewSubspace(M);
        print "Dimension of space of modular forms n =", Dimension(M);
        print "Dimension of space of newforms n_new =", Dimension(NewM);
        print "=======";
    end for;
    print "++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;
