// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.26-10

// The code in this file contains a function to compute the possible levels after level-lowering
// We follow the method of Freitas and Siksek presented in their paper:
// N. Freitas and S. Siksek. Fermat's last theorem over some small real quadratic fields. Algebra Number Theory, 9(4):875–895, 2015.

// We run the function in this file in the "levels.m" file, available at
// https://github.com/michaud-jacobs/thesis/blob/main/flt/levels.m
// (the function is in a separate file so it can be loaded from other files)

////////////////////////////////////////////

// Input: Squarefree d > 0
// Output:
// List of possibilities for the level-lowered levels N_p, sorted by norm
// The quadratic field K = Q(sqrt_d)
// Set S of prime ideals in K above 2
// Set H of representatives for Cl(K) / Cl(K)^2

Np_possibilities := function(d);
    T<x>:=PolynomialRing(Rationals());
    K<sqrt_d>:=NumberField(x^2-d);
    OK:=RingOfIntegers(K);
    ClK,mu:=ClassGroup(K);
    muinv:=mu^(-1);
    Fac_2:=Factorisation(2*OK);  // prime factorisation of the ideal 2O_K
    S:=[Fac_2[i][1] : i in [1..#Fac_2]];   // The set of primes above 2.
    QuoClK,nu:=quo<ClK | 2*ClK>;   // the quotient group  Cl(K) / 2*Cl(K)
    elts:=[q : q in QuoClK];
    H:=[1*OK];
    // We choose a representative for Cl(K) / 2*Cl(K) when this group is non-trivial
    for i in [2..#QuoClK] do
        primes := [P : P in PrimesUpTo(40,K) | IsOdd(Norm(P)) and nu(muinv(P)) eq elts[i]]; // find some prime representatives for the element of Cl(K) / 2*Cl(K) 
        _,n:=Minimum([Norm(P) : P in primes]); // choose a representative of minimal norm
        H_i:=primes[n];
        if d eq 65 then
            H_i := primes[n+1]; // We choose a different prime in the case d = 65 (better for the elimination step)
        end if;
        H:=H cat [H_i];
    end for;              // H forms a set of representatives for Cl(K)/Cl(K)^2, with #H=r.

    // We now follow Freitas and Siksek's strategy to calculate a list of possible levels N_p.
    // We first compute possibilities for the even part of the level.

    R<y>:=PolynomialRing(K);
    rams:=[Fac_2[i][2] : i in [1..#Fac_2]];
    b:=&*[(S[i])^(2*rams[i]+1) : i in [1..#Fac_2]];  // ideal b is as in Freitas and Siksek's paper
    OKb,pi:=quo<OK | b>; // quotient of OK by the ideal b
    U,t:=UnitGroup(OKb);
    s:=t^(-1);

    Sq:={oo^2 : oo in OKb | IsUnit(oo)};
    SFU,w:=quo<U |s(Sq)>; // units in OKb modulo squares
    
    // We continue to follow Freitas and Siksek's method

    Uni,psi:=UnitGroup(OK);
    UniGens:=SetToIndexedSet(Generators(Uni)); // generators for unit group of OK
    imphi:=[pi(psi(gg)): gg in UniGens | IsUnit(pi(psi(gg)))]; // elements that generate image of map called Psi in Freitas-Siksek
    Coker, v := quo<SFU | w(s(imphi))>;
    reps:=[(t(  (cc @@ v   ) @@ w)) @@ pi : cc in Coker]; // representatives for the cokernel of the map called Psi in Freitas-Siksek 
    
    // We now wish to scale these representatives by units of OK, to find the best set of representatives
    // If u_1, u_2, ..., u_g denote the generators of the unit group of OK
    // then we multiply our reps by (u_1^e_1)(u_2^e_2) ... (u_g^e_g)
    // where each e_i can take the value 0 or 1.
    
    g:=#UniGens;
    list:=[**];
    for jj in [0..(2^g)-1] do
        l1:=Intseq(jj,2);  // the binary representation of jj, this will allow us to find the appropriate list of 0s and 1s
        if g gt #l1 then
            l2:=l1 cat ZeroSequence(Integers(),g-#l1); // pad out with zeros
        end if;
        if g eq #l1 then
            l2:=l1;
        end if;
        list:=list cat [*l2*];
    end for;
    sfunits:=[];
    for l in list do
        sfunit:=&*[(psi(UniGens[i]))^(l[i]) : i in [1..#UniGens]];  // one choice of (u_1^e_1) ... (u_g^e_g)
        sfunits:=sfunits cat [sfunit];
    end for;

    Lambdas:=[**]; // list of possible sequences of representatives for the cokernel of the map called Psi in Freitas-Siksek
    // We scale our existing representatives (reps) by all possible units up to squares
    for i in [1..#reps] do
        lambi:=[sfunits[j]*reps[i] : j in [1..#sfunits]];
        Lambdas:=Lambdas cat [*lambi*];
    end for;
    
    // we now see which set of representatives from the Lambdas to pick

    newreps:=[];
    Npevens:=[];
    for i in [1..#reps] do
        Npevensi:=[];
        for j in [1..#sfunits] do
            rootlam:=y^2-Lambdas[i][j];
            exps:=[];
            for k in [1..#S] do
                if IsIrreducible(rootlam) eq true then
                    L := NumberField(rootlam);
                    OL:=RingOfIntegers(L);
                    D:=Discriminant(OL);
                    v:=Valuation(D, S[k]);     // check valuation of discriminant of K_p (root(lambda)) / K_p, as in Freitas-Siksek
                    if v eq 0 then
                        e:=1;
                    end if;
                    if v gt 0 then
                        e:=2*v;
                    end if;
                end if;
                    if IsIrreducible(rootlam) eq false then
                        e:=1;
                    end if;
                    exps:=exps cat [e];
            end for;
            Npeven:=&*[S[j]^(exps[j]): j in [1..#S]]; 
            Npevensi:=Npevensi cat [Npeven];
        end for;
        _,pos:=Minimum([Norm(n): n in Npevensi]); // identify minimum norm
        newreps:=newreps cat [Lambdas[i][pos]]; // choose corresponding coset representatives
        Npevens:=Npevens cat [Npevensi[pos]]; // choose the level of minimum norm
    end for;
    newrepsK:=[K ! (OK ! newreps[i]) : i in [1..#newreps]];
    Vals:= [   [Valuation(Npevens[i],S[j]) : i in [1..#reps]]   : j in [1..#S]];

    Npevset:=IndexedSet(Npevens); // Possibilities for the even part of N_p, when 2 is not inert in K.

    if IsInert(2,OK) eq true then
        Npevset:= Npevset join {S[1]^4};
    end if;

    // Combine even and odd part of N_p to give a list of possibilities for N_p.

    N_ps:={};
    for i in [1..#H] do
        for j in [1..#Npevset] do
            Np:=((H[i])^2)*(Npevset[j]);
            N_ps:=N_ps join {Np};
        end for;
    end for;
    N_ps:=Sort(IndexedSet(N_ps));   // A list of the possible levels N_p, ordered by norm
    return N_ps, K, S, H;
end function;

// (We run the function in the "levels.m" file)
