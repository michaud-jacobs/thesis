// Magma code to support the computations in the paper On elliptic curves with p-isogenies over quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/p-isog-quadratic for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is at the end of the file


// This code verifies the computations in part of the proof of Theorem 2  (for d = 6 and d = -5)
// We compute a set of bad primes in the case of non-constant isogeny signature

non_const := function(d); 
    print("Considering d = "),d;
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

    aux := [q : q in PrimesInInterval(2,10) | IsSplit(q,OK)]; // a prime that doesn't split will not bound p

    Resus:= [];

    for q in aux do
        qq := Factorisation(q*OK)[1][1];
        nq := q; // since q splits
        r := Order(phi(qq));
        _,al := IsPrincipal(qq^r);
        Aq:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] ]; 
    
        Rq := q*LCM([Integers() ! (Norm (Resultant(y^2-a*y+nq,y^(12*r)-al^(12)))) : a in Aq]); // pot. good. red. 
    
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

// At this point, a finer sieve can be applied.
// To do this, include the commented code into the function.

/*    /////////////////////////////////////////////////////////////////////

badpp := [];

for p in [p : p in badp | p notin vbadp] do 
    ct := 0;
    S<z> := PolynomialRing(GF(p));
    for q in aux do
        if q eq p then 
            continue;  // move on to next q
        end if;
        q1 := Factorisation(q*OK)[1][1];
        q2 := Factorisation(q*OK)[2][1];
        r := Order(phi(q1)); 
        _,al1 := IsPrincipal(q1^r);
        _,al2 := IsPrincipal(q2^r);
            
        nq:=q; 
        Aq:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] ]; 
        Apq := [ a : a in Aq | IsSquare(GF(p) ! (a^2-4*nq)) ]; // include trace condition
        a_ct := [];

        Mqp := [GF(p) ! (Integers() ! (Norm(al1^(12)-1))), GF(p) ! (Integers() ! (Norm( al2^(12)-nq^(12*r) ))) ];
        if IsZero(Mqp[1]) or IsZero(Mqp[2]) then  
           a_ct := a_ct cat [1];
        end if;

        p0 := Factorisation(p*OK)[1][1];
        Quo,red := ResidueClassField(p0);
        redal1 := red(al1);
        redal2 := red(al2);        

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
                 Bda1 := [root1^(12*r)-redal1^(12),root2^(12*r)-redal2^(12)];  
                 Bda2 := [root1^(12*r)-redal2^(12),root2^(12*r)-redal1^(12)];  
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
    end for;
    if ct eq 0 then 
       badpp := badpp cat [p];
    end if;
end for;

print("Final bad primes are : "), Set(Sort(badpp cat vbadp));
print("++++++++++++++++++++");
*/

/* Output for d in [-5,6]

Considering d =  -5
{ 2, 3, 5, 7, 11, 13, 17, 19, 37, 43 }

Considering d =  6
{ 2, 3, 5, 7, 11, 13, 17, 19, 37 }
*/

