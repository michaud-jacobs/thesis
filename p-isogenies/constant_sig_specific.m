// Magma code to support the computations in the paper On elliptic curves with p-isogenies over quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/p-isog-quadratic for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is at the end of the file


// This code verifies the computations parts of the proofs of Theorem 5.3 and Proposition 5.5
// We compute a set of bad primes in the case of constant isogeny signature

// To verify the computations in Theorem 5.3, simply run the code for d := 5 and set aux := [3,2].
// The primes 2 and 3 are inert in Q(sqrt(5)) and this will therefore replicate the set-up exactly

const := function(d: aux_upper_bd := 20, t := 1); // to work over the field K = Q(sqrt(d))
    T<x>:=PolynomialRing(Rationals());
    K<a>:=NumberField(x^2-d);
    OK:=RingOfIntegers(K);
    ClK, pi := ClassGroup(K);
    phi := pi^(-1);
    vbadp := [2,3,5,7,11,13,17,19,37];
    aux := PrimesInInterval(3,aux_upper_bd) cat [2];

    Resus:=[];
    for q in aux do

        if q eq 2 then
            largep := [p : p in PrimeFactors(GCD(Resus)) | p gt 2357] ;
            if largep ne []  then  // (q,p) may not be an admissible pair
                print("large p after initial sieve are "),largep;
                break;
            end if;
        end if;

        qq := Factorisation(q*OK)[1][1];
        r := Order(phi(qq)); // will be 1 for all inert primes.
        nq:=Norm(qq);


        Aqt :=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1-a) mod t)];

        Rq := q*LCM([Integers() ! (Resultant(x^2-a*x+nq,x^(12*r)-1)) : a in Aqt]);
        if q eq 2 and nq eq q then // need to consider reduction to (\infty, 0)
           m2 := 2^(12*r)-1;
           Rq := LCM([Rq,m2]);
        end if;
        if q eq 2 then
             Rq := LCM([Rq,41]);
        end if;
        Resus:=Resus cat [Rq];
    end for;

    badp:=[p : p in PrimeFactors(GCD(Resus))];
    return Set(Sort(badp cat vbadp));
end function;

for d in [5,47*67*101] do // Output at end of file.
    specif_sig(d);
end for;

/* Output for d in [5, 47*67*101]

Considering d =  5
{ 2, 3, 5, 7, 11, 13, 17, 19, 37 }

Considering d =  318049
{ 2, 3, 5, 7, 11, 13, 17, 19, 37 }

*/
