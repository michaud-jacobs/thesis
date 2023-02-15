// We compute formal immersion matrices
// Tests formal immersion criterion for N = mp for a prime m.

m := 2;
for p in PrimesInInterval(17,100) do
    // print "p = ", p;
    N := m*p;
    S:=CuspForms(N);
    R<q>:=PowerSeriesRing(Integers());
    J:=JZero(N);
    dec := Decomposition(J);
    Nfs := [* *];
    for d in dec do
        if IsZeroAt(LSeries(d),1) eq false then
            Nfs := Nfs cat [*Newform(d)*];
        end if;
    end for;

    basis := [ ];
    for f in Nfs do
        K:= CoefficientField(f);
        RK:= ChangeRing(R,K);
        SK:= BaseChange(S,K);
        prec := Max(100,Ceiling(N /3));
        fexp := qExpansion(f,prec); // Increase precision to uniquely determine form
        fK:= SK ! (RK ! fexp);
        OK := Integers(K);
        if Degree(K) eq 1 then
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

    CuspExps:=[*basis*]; // Initial list
    ALs:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
    for m in ALs do
        CE:=[* *];
        for f in basis do
            fm:=AtkinLehnerOperator(m,f);
            CE:= CE cat [*fm*];
        end for;
        CuspExps:=CuspExps cat [*CE*];
    end for;

    for i in [1,2,3,4] do
        Cusp2 := i; // i <--> ALs[i](infinity) for i = 2,3,4.
        Col1 := [Integers() ! Coefficient(f,1) : f in CuspExps[1]];
        if i eq 1 then
            Col2 := [Integers() ! Coefficient(f,2) : f in CuspExps[1]];
        else
            Col2 := [Integers() ! Coefficient(f,1) : f in CuspExps[Cusp2]];
        end if;
        M := Transpose(Matrix(Integers(), [Col1,Col2]));
        gcdMinors := GCD(Minors(M,2));
        if IsZero(gcdMinors) or IsSubsequence(PrimeFactors(gcdMinors),[2]) eq false then
            print "Criterion failed for N =", N, "and cusp =", i;
            // M;
        end if;
    end for;
    // print("+++++++++++++++++++++");
end for;
