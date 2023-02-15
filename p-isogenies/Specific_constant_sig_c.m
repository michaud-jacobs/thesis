// Magma code to support the computations in the paper On elliptic curves with p-isogenies over quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/p-isog-quadratic for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is at the end of the file


// This code verifies the computations parts of the proofs of Theorem 5.3 and Proposition 5.5
// We compute a set of bad primes in the case of constant isogeny signature

// To verify the computations in Theorem 5.3, simply run the code for d := 5 and set aux := [3,2].
// The primes 2 and 3 are inert in Q(sqrt(5)) and this will therefore replicate the set-up exactly

specif_sig := function(d); // to work over the field K = Q(sqrt(d))
    print("Considering d = "),d;
    T<x>:=PolynomialRing(Rationals());
    K<a>:=NumberField(x^2-d);
    OK:=RingOfIntegers(K);
    ClK, pi := ClassGroup(K);
    phi := pi^(-1); 
    vbadp := [2,3,5,7,11,13,17,19,37]; 
    
    aux :=  PrimesInInterval(3,20) cat [2];
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
    
     
        Aq:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] ]; 
    
        Rq := q*LCM([Integers() ! (Resultant(x^2-a*x+nq,x^(12*r)-1)) : a in Aq]);  
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

// At this point, a finer sieve can be applied.
// To do this, included the commented code into the function

/*    /////////////////////////////////////////////////////////////////////

    badpp := []; // we now apply the finer sieve

    for p in [p : p in badp | p notin vbadp] do 

        ct := 0;
        S<z> := PolynomialRing(GF(p)); // work mod p for resultants as it is faster.
        for q in aux do
            if q eq p or (q eq 2 and p gt 2357) or (q eq 2 and p = 41) then // q = p or (q,p) is not admissible
                continue;  // so move on to next q
            end if;  
       
            qq := Factorisation(q*OK)[1][1];
            r := Order(phi(qq)); 
            nq:=Norm(qq);  

            if q eq 2 and nq eq q and IsZero( (2^(12*r) - 1) mod p) then // issue with multiplicative reduction at primes above 2
                   continue;
            end if;


            Aq :=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] ];         
            Apq := [ a : a in Aq | IsSquare(GF(p) ! (a^2-4*nq)) ]; // include trace condition

            a_ct := [];

            if #Apq eq 0 then
                a_ct := [0];
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
                         a_ct := a_ct cat [0];
                     else a_ct := a_ct cat [1];
                     end if;
                 end for;
            end if;
            if IsZero(a_ct) then // all tests passed using this q
                ct := ct + 1;
                break;
            end if;
        end for; // q loop
        if ct eq 0 then 
            badpp := badpp cat [p];
        end if;
    end for;  // p loop

    print("Final bad primes are : "), Set(Sort(badpp cat vbadp));
    print("++++++++++++++++++++");
end for;  // d loop
*/

/* Output for d in [5, 47*67*101]

Considering d =  5
{ 2, 3, 5, 7, 11, 13, 17, 19, 37 }

Considering d =  318049
{ 2, 3, 5, 7, 11, 13, 17, 19, 37 }

*/
