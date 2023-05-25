// Magma code to support the computations in my PhD thesis.

// This code verifies certain formal immersion criteria

////////////////////////////////////////////

// Input: m = 2 or 3 and a prime p >= 17
// if m = 2 then p should not be 23

// Output: true or false
// true if formal immersion check true for N = mp for each q > 2 with q ne m and q ne p
// false if formal immersion check fails for N = mp for some q and some cusp
// (if false then function prints a statement too)

check_formal_immersion := function(m,p);
    N := m*p;
    // We first choose the newforms which correspond to abelian varieties with rank 0 over Q
    S:=CuspForms(N);
    R<q>:=PowerSeriesRing(Integers());
    J:=JZero(N);
    dec := Decomposition(J);
    Nfs := [* *];
    for d in dec do
        if IsZeroAt(LSeries(d),1) eq false then  // We pick out newform orbits with rank 0
            Nfs := Nfs cat [*Newform(d)*];
        end if;
    end for;

    basis := [ ];  // We seek a basis with integer Fourier coefficients
    for f in Nfs do
        K:= CoefficientField(f);
        RK:= ChangeRing(R,K);
        SK:= BaseChange(S,K);
        prec := Max(100,Ceiling(N /3)); // found this precision bound to be sufficient in cases tested
        fexp := qExpansion(f,prec); // can increase precision to uniquely determine form if necessary
        fK:= SK ! (RK ! fexp);
        OK := Integers(K);
        if Degree(K) eq 1 then // Rational field
            int_bas := Basis(OK);
        else
            int_bas := Basis(Codifferent(1*OK));
        end if;
        for b in int_bas do
            bfK := b*fK;
            tr_bfK := S ! (R ! (&+[Trace(Coefficient(bfK,i))*q^i : i in [1..prec-1]] + O(q^(prec-1))));
            basis := basis cat [tr_bfK];
        end for;
    end for;

    CuspExps:=[*basis*]; // Initial list, we now compute expansions at other cusps
    ALs:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1]; // Atkin-Lehner indices
    for m in ALs do
        CE:=[* *];
        for f in basis do
            fm:=AtkinLehnerOperator(m,f); // expansion at the cusp w_m(infty)
            CE:= CE cat [*fm*];
        end for;
        CuspExps:=CuspExps cat [*CE*];
    end for;

    for i in [1,2,3,4] do  // We now form the formal immersion matrices
        Cusp2 := i; // i <--> ALs[i](infinity) for i = 2,3,4.
        Col1 := [Integers() ! Coefficient(f,1) : f in CuspExps[1]]; // first column of matrix
        // second column is defined according to whether we have a double cusp or not
        if i eq 1 then
            Col2 := [Integers() ! Coefficient(f,2) : f in CuspExps[1]];
        else
            Col2 := [Integers() ! Coefficient(f,1) : f in CuspExps[Cusp2]];
        end if;
        M := Transpose(Matrix(Integers(), [Col1,Col2])); // Formal immersion matrix
        gcdMinors := GCD(Minors(M,2)); // use this to check rank mod q for many q > 2
        if IsZero(gcdMinors) or IsSubsequence(PrimeFactors(gcdMinors),[2]) eq false then
            print "Criterion failed for N =", N, "and cusp =", i;
            print "Not testing further cusps";
            return false;
        end if;
    end for;
    return true; // No cusps failed, so formal immersion criterion passed
end function;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// We check the formal immersion criterion for m = 2, 3 and primes 17 <= p <= 300
// (if m = 2 then p ne 23)

time for m in [2,3] do
    for p in PrimesInInterval(17,300) do // max prime is 293
        if p eq 23 and m eq 2 then
            continue; // result does not apply in this case
        end if;
        assert check_formal_immersion(m,p);
    end for;
end for;

// Runtime: total time = approx 3.5 hours
// (computations with p > 150 are somewhat slow)
