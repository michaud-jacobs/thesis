// Magma code to support the computations in my PhD thesis.

// The code in this file provides functions for carrying out the main elimination of newforms step.

// We run the functions in this file in the "newform_elimination.m" file, available at
// https://github.com/michaud-jacobs/thesis/blob/main/flt/newform_elimination.m
// (the functions are in a separate file so they can be loaded from other files)

// The code uses the function "Np_possibilities" from the file "levels_function.m" available at:
// https://github.com/michaud-jacobs/thesis/blob/main/flt/levels_function.m

load "levels_function.m";

////////////////////////////////////////////

// This code attemptes to eliminate all newforms at all possible levels
// There are two functions for this, hecke_elim and decomp_elim

// hecke_elim works directly with Hecke operators to compute partial newform data.
// As the levels get larger (say > 200) it is much faster.
// As the levels get even larger (say >1000), it is the only (reasonable) option.

// decomp_elim computes the full newform decompositions.
// It should only be used on spaces of smaller dimensions.
// It has a greater chance of eliminating primes than hecke_elim

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// auxiliary function to compute c-values
// q a prime ideal, e a polynomial. Outputs corresponding c-value.

c_val_qe := function(q,e);
    nq := Norm(q);
    A := [a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1 - a) mod 4)]; // the set A_{q,4}
    C1 := nq * Evaluate(e,nq+1) * Evaluate(e,-nq-1) * (&*[Evaluate(e,-a) : a in A]);
    C := AbsoluteValue(Integers() ! C1 );
    return C;
end function;

// hecke_elim works directly with Hecke operators to try and eliminate newforms
// Input: Level Np and quadratic field K
// Output:
// Vs: subspaces of the space of newforms that were not eliminated0
// Cs: corresponding c-values of these subspaces
// Es: corresponding characteristic polynomials of these subspaces
// T: list of primes used

hecke_elim := function(Np,K);
    M := HilbertCuspForms(K, Np);
    NewM := NewSubspace(M);
    normbd := 150;   // Increase this bound to enlarge T
    pbd := 13;       // If all prime divisors of a c-value are <= pbd, then the subspace is eliminated.
    // we first choose the auxiliary primes q to use
    T1 := [q : q in PrimesUpTo(normbd,K) | (Valuation(Np,q) eq 0) and IsSplit(q) ];
    T1 := [T1[i] : i in [1..#T1] | IsOdd(i)]; // Choose only one prime above q if q splits
    T2 := [q : q in PrimesUpTo(normbd,K) | (Valuation(Np,q) eq 0) and (IsSplit(q) eq false ) ]; 
    T:=Sort(T1 cat T2); // sorted by norm
    print "Using", #T, "primes";
    print "Computing first Hecke operator";
    H1:=HeckeOperator(NewM,T[1]);
    M1:=Matrix(H1);
    print "Factorising its characteristic polynomial";
    Chpoly1:=Factorisation(CharacteristicPolynomial(H1));

    Cs:=[*c_val_qe(T[1],e[1]) : e in Chpoly1*]; // The c-values of the subspaces
    // We eliminate subspaces if all prime factors of the c-value are <= pbd
    Newind:=[i : i in [1..#Cs] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))]; // indices of subspaces that cannot be eliminated
    Cs:=[*Cs[i] : i in Newind*]; // c-values of subspaces that cannot be eliminated
    Es:=[* [Chpoly1[i][1]] : i in Newind*]; // char poly factors of subspaces that cannot be eliminated
    Vs:=[* *]; // list of supbspaces that cannot be eliminated
    print "Computing first Hecke decomposition";
    for j in Newind do   // Start by computing the list of subspaces corresponding to the first Hecke operator
        V := NullSpace(Evaluate(Chpoly1[j][1],M1)); // subspace corresponding to char poly factor
        Vs := Vs cat [* V *];
    end for;
    print "Computing further Hecke decompositions";
    for i in [2..#T] do
        H:=HeckeOperator(NewM,T[i]);
        M:=Matrix(H);
        // prepare new lists
        NVs:=[* *];
        NCs:=[* *];
        NEs:=[* *];
        for j in [1..#Vs] do // we break down each existing subspace
            B:=Basis(Vs[j]);
            Coords:=[Coordinates(Vs[j],H(B[k])) : k in [1..#B]   ]; // apply Hecke operator to basis elements
            NM:=Matrix(Coords); // Hecke operator on the subspace
            Chpoly:=Factorisation(CharacteristicPolynomial(NM));
            // prepare new lists for this subspace
            NVsj:=[* *];
            NCsj:=[* *];
            NEsj:=[* *];
            for e in Chpoly do
                basns:= Basis(  NullSpace( Evaluate(e[1],NM) )  );
                subsp:= sub< Vs[j] | [ &+[basns[l][k]*B[k] : k in [1..#B] ]  :  l in [1..#basns] ]>;
                NVsj:=NVsj cat [* subsp *]; // add new subspace to list
                NC:= GCD(  Cs[j],c_val_qe(T[i],e[1])   ); // gcd of previous c-value and new c-value
                NCsj:=NCsj cat [* NC *]; // add c-value to list
                Ne:=Es[j] cat [e[1]]; 
                NEsj:=NEsj cat [* Ne *];
            end for;
            NVs:=NVs cat NVsj;
            NCs:=NCs cat NCsj;
            NEs:=NEs cat NEsj;
        end for;
        // We have now formed our subspace decomposition and we attempt to eliminate subspaces
        Vs:=NVs;
        Cs:=NCs;
        Es:=NEs;
        // We now eliminate subspaces
        Vs:=[*Vs[i] : i in [1..#Vs] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))*];
        Es:=[*Es[i] : i in [1..#Es] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))*];
        Cs:=[*Cs[i] : i in [1..#Cs] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))*];
        if #Vs eq 0 then
            print "All spaces eliminated";
            return Vs, Cs, Es, T;
        end if;
    end for;
    print "Spaces remaining, unable to eliminate the following primes:", Cs; // (look at the prime factors of the leftover numbers)
    return Vs, Cs, Es, T;
end function;

////////////////////////////////////////////////////////////////////////////////////////

// decomp_elim computes the full newform decomposition to try and eliminate newforms
// Input: Level Np, quadratic field K, normbd (to control how many primes to use)
// Output:
// CNpprimes: primes that were not eliminated,
//            a zero means no primes were eliminated for the corresponding form
// bad_f: a list of newforms with C_value = 0
// T: list of primes used

decomp_elim := function(Np,K,normbd);
    M := HilbertCuspForms(K, Np);
    NewM:=NewSubspace(M);
    decomp := NewformDecomposition(NewM); // the full newform decomposition
    CNpfs:=[];  // build up to list of C-values
    CNpPrimes:=[]; // prime factors of the C-values
    bad_f := [* *]; // newforms which we cannot eliminate
    for i in [1..#decomp] do
        f:=Eigenform(decomp[i]); // Hilbert newform
        Q_f:=HeckeEigenvalueField(decomp[i]);
        OQ_f:=Integers(Q_f);
        T := [q : q in PrimesUpTo(normbd,K) |Valuation(Np,q) eq 0 ]; // auxiliary primes q to use
        Bqfs:={};
        for q in T do
            nq:=Norm(q);
            aqf:=HeckeEigenvalue(f,q);
            A:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1 - a) mod 4)];
            Bqf1:=nq*((nq+1)^2-aqf^2);
            Bqf2:=&*[a-aqf: a in A];
            Bqf:=(Bqf1*Bqf2)*OQ_f;
            Bqfs:=Bqfs join {Bqf};
        end for;
        Bf:=&+Bqfs;
        if Bf ne 0*OQ_f then
           CNpf:=Norm(Bf);
           CNpfPrimes:=PrimeFactors(CNpf);
        else CNpf:=0;
             CNpfPrimes:=[0];
             bad_f := bad_f cat [* f *];
        end if;
        CNpPrimes:=CNpPrimes cat CNpfPrimes;
        CNpfs:=CNpfs cat [CNpf];
    end for;
    CNpred:=SetToSequence(Set(CNpfs));
    CNpPrimes:=SetToSequence(Set(CNpPrimes));
    return CNpPrimes, bad_f, T;
end function;

// (We run the functions in the "newform_elimination.m" file)
