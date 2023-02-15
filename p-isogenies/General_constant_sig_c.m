// Magma code to support the computations in the paper On elliptic curves with p-isogenies over quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/p-isog-quadratic for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is at the end of the file


// This code verifies the computations in the proof of Theorem 1

gen_const := function(n: aux_upper_bd := 20, t := 1);  // n is the class group exponent.
    print("Considering n = "),n;

    T<x> := PolynomialRing(Rationals());
    vbadp := [2,3,5,7,11,13,17,19,37];

    aux := PrimesInInterval(3,aux_upper_bd) cat [2]; // start with primes > 2 and finish with 2 (if(2,p) is admissible).

    Resus:=[];
    for q in aux do
          if q eq 2 then
             largep := [p : p in PrimeFactors(GCD(Resus)) | p gt 2357] ;
             if largep ne [] then  // (q,p) may not be an admissible pair
                print("large p after initial sieve are "),largep;
                break;
             end if;
          end if;

          pairs := [ [q^2,1] ] cat [[q,r] : r in [1..n] | IsZero(n mod r) ]; // possibilities for (nq,r)
          Rqs := [];
          for pair in pairs do
              nq := pair[1];
              r := pair[2];
              Aqt :=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1-a) mod t)];
              Rq := q*LCM([Integers() ! (Resultant(x^2-a*x+nq,x^(12*r)-1)) : a in Aqt]);
              if q eq 2 and nq eq q then // need to consider reduction to (\infty, 0)
                 m2 := 2^(12*r)-1;
                 Rq := LCM([Rq,m2]);
              end if;
              Rqs := Rqs cat [Rq];
          end for;
          if q eq 2 then
             Rqs := Rqs cat [41];
          end if;
          Resus := Resus cat [LCM(Rqs)];

    end for;
    badp:=[p : p in PrimeFactors(GCD(Resus))];
    return Set(Sort(badp cat vbadp));
end function;

for n in [1,2,3] cat [100] do   // Output at end of file.
    gen_sig(n);
end for;

/* Output for n in [1,2,3] cat [100]:

Considering n =  1
{ 2, 3, 5, 7, 11, 13, 17, 19, 37 }

Considering n =  2
{ 2, 3, 5, 7, 11, 13, 17, 19, 37 }

Considering n =  3
{ 2, 3, 5, 7, 11, 13, 17, 19, 37, 73 }

Considering n =  100
{ 2, 3, 5, 7, 11, 13, 17, 19, 31, 37, 41, 61, 97, 101, 151, 241, 401, 601, 1201, 1801 }

*/
