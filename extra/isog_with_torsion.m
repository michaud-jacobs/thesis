gen_sig_t := function(n,t);  // n is the class group exponent, t divides size of torsion.
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
              Aq:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))]  | IsZero((nq+1-a) mod t)  ];
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




non_const_t := function(d,t);
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

    aux := [q : q in PrimesInInterval(2,50) | IsSplit(q,OK)]; // a prime that doesn't split will not bound p

    Resus:= [];

    for q in aux do
        qq := Factorisation(q*OK)[1][1];
        nq := q; // since q splits
        r := Order(phi(qq));
        _,al := IsPrincipal(qq^r);
        Aq:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1-a) mod t)];

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
