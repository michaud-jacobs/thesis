// Magma code to support the computations in my PhD thesis.

// The code computes bad primes in the case of a constant isogeny signature
// works over a specific quadratic field K = Q(sqrt(d))

////////////////////////////////////////////

// Input: d
// We work over the quadratic field K = Q(sqrt(d))
// Optional input: aux_upper_bd and t
// aux_upper_bd is an upper bound for the primes q to be used (default = 20)
// t is a positive integer that divides the size of E(K)_tors (default = 1)

// Output: list of bad primes for constant isogeny signature
// list will automatically include [2,3,5,7,11,13,17,19,37]

const := function(d: aux_upper_bd := 20, t := 1); // to work over the field K = Q(sqrt(d))
    T<x>:=PolynomialRing(Rationals());
    K<a>:=NumberField(x^2-d);
    OK:=RingOfIntegers(K);
    ClK, pi := ClassGroup(K);
    phi := pi^(-1);
    vbadp := [2,3,5,7,11,13,17,19,37]; // primes to automatically include
    aux := PrimesInInterval(3,aux_upper_bd) cat [2];

    Resus:=[]; // build up to sequence of the Rqs, one per prime q
    for q in aux do
        if q eq 2 then
            largep := [p : p in PrimeFactors(GCD(Resus)) | p gt 2357] ; // bound coming from formal immersion criterion
            if largep ne []  then  // (q,p) may not be an admissible pair
                print("large p after initial sieve are "),largep;
                break;
            end if;
        end if;

        qq := Factorisation(q*OK)[1][1];
        r := Order(phi(qq)); // will be 1 for all inert primes.
        nq:=Norm(qq);

        Aqt :=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1-a) mod t)]; // possible traces of Frobenius
        Rq := q*LCM([Integers() ! (Resultant(x^2-a*x+nq,x^(12*r)-1)) : a in Aqt]);
        if q eq 2 and nq eq q then // need to consider reduction to (\infty, 0)
           m2 := 2^(12*r)-1;
           Rq := LCM([Rq,m2]);
        end if;
        if q eq 2 then
             Rq := LCM([Rq,41]); // (2,41) is not admissible
        end if;
        Resus:=Resus cat [Rq];
    end for;

    badp:=[p : p in PrimeFactors(GCD(Resus))];
    return Set(Sort(badp cat vbadp));
end function;

////////////////////////////////////////////////////////////////////////////////

// We first check what happens if 2 and 3 are inert in K by running the following code
// (we set d = 5 since 2 and 3 are inert in Q(sqrt(5)))

assert const(5: aux_upper_bd := 3) eq {2,3,5,7,11,13,17,19,37};

// We now run the computation for d = 47*67*101

assert const(47*67*101) eq {2,3,5,7,11,13,17,19,37};
