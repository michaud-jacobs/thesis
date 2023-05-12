// Magma code to support the computations in my PhD thesis.

// The code computes bad primes in the case of a non-constant isogeny signature

////////////////////////////////////////////

// Input: d
// We work over the quadratic field K = Q(sqrt(d))
// Optional input: aux_upper_bd and t
// aux_upper_bd is an upper bound for the primes q to be used (default = 10)
// t is a positive integer that divides the size of E(K)_tors (default = 1)

// Output: list of bad primes for non-constant isogeny signature
// list will automatically include [2,3,5,7,11,13,17,19,37]

non_const := function(d: aux_upper_bd := 10, t := 1);
    T<x>:=PolynomialRing(Rationals());
    K<a>:=NumberField(x^2-d);
    S<y> := PolynomialRing(K);
    OK:=RingOfIntegers(K);
    ClK, pi := ClassGroup(K);
    n := Exponent(ClK);
    phi := pi^(-1);
    Uni,psi:=UnitGroup(OK);
    if d gt 0 then // real quadratic field case
        eps:=psi(Uni.2);  // a fundamental unit of K
        B:=PrimeFactors(Integers() ! (Norm(eps^12-1)));  // The prime factors of the quantity Norm(epsilon^12-1)
        B2 := [p : p in B | IsSplit(p,OK)]; // we can remove any inert primes
    else B := [];
        B2 := [];
    end if;
    vbadp := [2,3,5,7,11,13,17,19,37];

    aux := [q : q in PrimesInInterval(2,aux_upper_bd) | IsSplit(q,OK)]; // a prime q that does not split will not bound p

    Resus:= []; // build up to sequence of LCM(Mq,Rq), then p will divide the gcd of the sequence

    for q in aux do
        qq := Factorisation(q*OK)[1][1];
        nq := q; // since q splits
        r := Order(phi(qq));
        _,al := IsPrincipal(qq^r);
        Aqt:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1-a) mod t)];

        Rq := q*LCM([Integers() ! (Norm (Resultant(y^2-a*y+nq,y^(12*r)-al^(12)))) : a in Aqt]); // pot. good. red.

        Mq := q*( Integers() ! ( Norm(al^(12)-1)*Norm( al^(12)-q^(12*r) ) ) ); // pot. mult. red.

        Resus := Resus cat [LCM([Rq,Mq])];
    end for;

    badp:=[p : p in PrimeFactors(GCD(Resus)) | IsSplit(p,OK)]; // an inert prime will have constant isogeny signature
    if d gt 0 then
        badp := [p : p in B2 | p in badp];  // (badp should be a subset of B anyway)
    end if;

    return Set(Sort(badp cat vbadp));
end function;

////////////////////////////////////////////////////////////////////////////////

// We verify the computation for d = -5

assert non_const(-5) eq {2,3,5,7,11,13,17,19,37,43};
