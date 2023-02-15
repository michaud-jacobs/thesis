// Magma code to support the computations in the paper On elliptic curves with p-isogenies over quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/p-isog-quadratic for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is at the end of the file


// This code verifies the computations in the proof of Theorem 1

gen_sig := function(n);  // n is the class group exponent.
    print("Considering n = "),n;

    T<x> := PolynomialRing(Rationals());
    vbadp := [2,3,5,7,11,13,17,19,37]; 
    
    aux := PrimesInInterval(3,20) cat [2]; // start with primes > 2 and finish with 2 (if(2,p) is admissible).
    
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
              Aq:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))]];
              Rq := q*LCM([Integers() ! (Resultant(x^2-a*x+nq,x^(12*r)-1)) : a in Aq]);
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

// At this point, a finer sieve can be applied.
// To do this, include the commented code into the above function.

/* ///////////////////////////////////////////////
    
    badpp := [];  // we now apply the finer sieve

    for p in [p : p in badp | p notin vbadp] do 
        ct_p := 0;
        S<z> := PolynomialRing(GF(p)); // work mod p for resultants as it is faster.
        for q in aux do
            if q eq p or (q eq 2 and p gt 2357) or (q eq 2 and p eq 41) then // q = p or the pair (q,p) may not be admissible
               continue;  // so move on to next q
            end if;
              
            pairs := [ [q^2,1] ] cat [[q,r] : r in [1..n] | IsZero(n mod r) ];
            ct_q := [];
            for pair in pairs do
                nq := pair[1];
                r := pair[2];
                if q eq 2 and nq eq q and IsZero( (2^(12*r) - 1) mod p) then // issue with multiplicative reduction at primes above 2
                   ct_q := ct_q cat [1];
                   break;
                end if;

                Aq:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] ]; 
                Apq := [ a : a in Aq | IsSquare(GF(p) ! (a^2-4*nq))  ]; // include trace condition               
               
                if #Apq eq 0 then 
                   ct_q := ct_q cat [0];
                else for a in Apq do
                        frobroots := Roots(z^2-a*z+nq);
                        root1 := frobroots[1][1];
                        if #frobroots eq 2 then
                            root2 := frobroots[2][1];
                        else root2 := root1;
                        end if;
                        nqp := GF(p) ! nq;
                        Bda1 := [root1^(12*r)-1,root2^(12*r)-nqp^(12*r)];  
                        Bda2 := [root1^(12*r)-nqp^(12*r),root2^(12*r)-1];
                        if IsZero(Bda1) eq false and IsZero(Bda2) eq false then                    
                            ct_q := ct_q cat [0];
                        else ct_q := ct_q cat [1];
                        end if;
                    end for;
                end if;            
            end for;  // pair loop
            if IsZero(ct_q) then // all tests passed using this q both times round
                ct_p := ct_p + 1;
                break q;  // p is eliminated
            end if;
        end for; // q loop
        if ct_p eq 0 then // no prime q worked
           badpp := badpp cat [p]; 
        end if;
    end for;  // p loop

    print("Final bad primes are : "), Set(Sort(badpp cat vbadp));
    print("++++++++++++++++++++");

end for;  // n loop
*/

/*
Alternative code to run through all elliptic curves defined over the residue field to compute a set of possible values for a_q(E)
Aqs := function(nq);
    F := FiniteField(nq);
    A := {};
    for j in F do
        Ej := EllipticCurveWithjInvariant(j);
        if IsZero(j) or IsZero(j-1728) then        
           A := A join {TraceOfFrobenius(Et) : Et in Twists(Ej) };
        else t:=TraceOfFrobenius(Ej);
           A := A join {t,-t};
        end if;
    end for;
    A := Sort(SetToSequence(A));
    return(A);
end function;
*/

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

