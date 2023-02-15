// Magma code to support the computations in the paper On elliptic curves with p-isogenies over quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/p-isog-quadratic for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is at the end of the file


// This code verifies the computations in part of the proof of Theorem 2  (for d = 6 and d = -5)
// We compute a set of bad primes in the case of non-constant isogeny signature

non_const := function(d: aux_upper_bd := 10, t := 1);
    T<x>:=PolynomialRing(Rationals());
    K<a>:=NumberField(x^2-d);
    S<y> := PolynomialRing(K);
    OK:=RingOfIntegers(K);
    ClK, pi := ClassGroup(K);
    n := Exponent(ClK);
    phi := pi^(-1);
    Uni,psi:=UnitGroup(OK);
    if d gt 0 then
        eps:=psi(Uni.2);  // a fundamental unit of K
        B:=PrimeFactors(Integers() ! (Norm(eps^12-1)));  // The prime factors of the quantity Norm(epsilon^12-1)
        B2 := [p : p in B | IsSplit(p,OK)];
    else B := [];
        B2 := [];
    end if;
    vbadp := [2,3,5,7,11,13,17,19,37];

    aux := [q : q in PrimesInInterval(2,aux_upper_bd) | IsSplit(q,OK)]; // a prime that doesn't split will not bound p

    Resus:= [];

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

for d in [-5,6] do // Output at end of file.
    non_const(d);
end for;


/* Output for d in [-5,6]

Considering d =  -5
{ 2, 3, 5, 7, 11, 13, 17, 19, 37, 43 }

Considering d =  6
{ 2, 3, 5, 7, 11, 13, 17, 19, 37 }
*/
