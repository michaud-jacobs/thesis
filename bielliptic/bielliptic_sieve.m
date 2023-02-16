// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.26-10

// This file contains the sieving computations

////////////////////////////////////////////

// The output for VerboseLevel 0 is included at the end of this file AND in bielliptic_sieve_output.txt
// The output for VerboseLevel 2 is in bielliptic_sieve_output.txt
// The output for the example computations is in bielliptic_sieve_output.txt

// The file bielliptic_sieve_output.txt is available at
// https://github.com/michaud-jacobs/thesis/blob/main/bielliptic/bielliptic_sieve_output.txt

// The code to reproduce the example computations is included at the end of this file

// The code uses functions from the file "bielliptic_models.m" available at:
// https://github.com/michaud-jacobs/thesis/blob/main/bielliptic/bielliptic_models.m

////////////////////////////////////////////

// This function carries out the Mordell--Weil sieve
// The functions takes as input a value N and some optional parameters:

// if check_bad_d = true then the sieve tests values of d that are expected to fail (default = false)
// The VerboseLevel can be set at 0, 1, 2, or 3 (default = 0), which will print varying level of output
// The sieve tests all d in range_d (default = [-100..100])
// The maximum value of a prime l to be used is maxi_l (default = 1000)

// The function outputs two sets, failed_d and KnownBad
// failed_d consists of values d which we unexpectedly failed to eliminate
// KnownBad consists of values d for which we found a quadratic point in X_0(N)(Q(sqrt(d)))

// The function uses the 'model_and_map' and 'is_nonsing_mod_l' functions available in bielliptic_models.m

sieve := function(N: check_bad_d := false, VerboseLevel := 0, range_d := [-100..100], maxi_l := 1000 );
    print "N =", N;
    X, E, psi, B, w, cusp := model_and_map(N);
    if VerboseLevel ge 2 then
        print "++++++++++++++++++++++++";
        print "Basis of cusp forms used is:\n", B;
        print "++++++++++++++++++++++++";
        print "The Atkin-Lehner involution w_N is:\n", w;
        print "++++++++++++++++++++++++";
        print "X is:\n", X;
        print "++++++++++++++++++++++++";
        print "E is:\n", E;
        print "++++++++++++++++++++++++";
        print "The map psi is:\n", psi;
        print "++++++++++++++++++++++++++++++++++++++++++++++++";
    end if;
    M, mu, tf1, tf2 := MordellWeilGroup(E);
    assert tf1 and tf2;
    rankE, tf3 := Rank(E);
    assert rankE eq 1 and tf3;
    T := TorsionSubgroup(E);
    if N ne 65 then
        assert #TorsionSubgroup(E) eq 1;
        R := mu(M.1);
        Q := mu(0*M.1); // Identity on E
        n_range := [0];
        if VerboseLevel ge 2 then
            print "The point R =", R, "generates E(Q)";
            print "++++++++++++++++++++++++";
        end if;
    else R := mu(M.2);
        assert #TorsionSubgroup(E) eq 2;
        Q := mu(M.1);
        assert Order(Q) eq 2;
        if VerboseLevel ge 2 then
            print "The points R =", R, "and Q =", Q, "generate E(Q)";
            print "++++++++++++++++++++++++";
        end if;
        n_range := [0,1]; // We run the sieve using mR and mR + Q
    end if;

    // We search for suitable primes l to use in the sieve
    initial_ls := [l : l in PrimesInInterval(3,maxi_l) | IsZero(N mod l) eq false];
    // The upper bound of 1000 can be increased here
    ls := [];
    for l in initial_ls do
        Fl := GF(l);
        El:=ChangeRing(E,Fl);
        Rl:=El ! Eltseq(R);
        Gl:=Order(Rl);
        if Max(PrimeFactors(Gl)) le 7 then
            ls := ls cat [l];
        end if;
    end for;
    original_ls := ls;
    if VerboseLevel ge 1 then
       print "Primes l to use in sieve are:\n", ls;
       print "++++++++++++++++++++++++";
    end if;

    max_l := ls[1]; // We will record the maximum value of l used in sieve

    failed_d := {};
    KnownBad := {};

    for n in n_range do
        if N eq 65 and n eq 0 and VerboseLevel ge 1 then
            print "Sieving for the first case";
            print "++++++++++++++++++++++++";
        end if;
        if n eq 1 and VerboseLevel ge 1 then
            print "Sieving for the second case";
            print "++++++++++++++++++++++++";
        end if;
        if VerboseLevel ge 3 then
            print "Known d computed are:";
        end if;

        // We compute KnownBad values of d by computing psi*(tR) for small t
        for t in [-5..5] do
            dec := Decomposition(Pullback(psi,Place(t*R+n*Q)));
            d := Discriminant(Integers(ResidueClassField(dec[1][1])));
            if IsZero(d mod 4) then
                d := Integers() ! (d/4);
            end if;
            if d ne 1 and AbsoluteValue(d) lt 100 then
                KnownBad := KnownBad join {d};
            end if;
            if VerboseLevel ge 3 then
                print "When t = ", t, "d = ", d;
            end if;
        end for;
        if VerboseLevel ge 1 then
            print "Values of d that must fail sieve are:\n", KnownBad;
            print "++++++++++++++++++++++++";
        end if;

        // We run the sieve for each value of d
        for d in [d : d in range_d | d ne 0 and d ne 1 and IsSquarefree(d)] do
            if VerboseLevel ge 1 then
                print "Considering d =", d;
            end if;


            // if check_bad_d eq false we skip d in KnownBad as they should fail
            // if check_bad_d eq true we check them and ensure they fail
            if check_bad_d eq false and d in KnownBad then
                if VerboseLevel ge 1 then
                    print d, "is known to fail";
                    print "++++++++++++++++++++++++++++++++++++++++++++++++";
                end if;
                continue d;
            end if;

            // We include ramified primes at the start of the sequence of ls:
            ls := original_ls; // reset first
            ramif := [l : l in PrimeFactors(d) | IsZero(N mod l) eq false and l gt 2];
            extra_l := [l : l in ramif | l notin ls]; // Extra primes l we are including for this d
            if VerboseLevel ge 3 then
                print "Including l in", extra_l;
            end if;
            ls := SetToSequence({@ l : l in ramif cat ls @});
            // These primes will be removed before proceeding to the next value of d


            K := QuadraticField(d);
            OK := Integers(K);

            mls:=[* *];
            Gls:=[];
            if VerboseLevel ge 3 then
                print "Starting sieve";
            end if;
            i := 0;  // parameter for later
            Newms := "undefined"; // parameter for later
            for l in ls do
                if VerboseLevel ge 3 then
                    print "Using l =", l;
                    if IsSplit(l,OK) then
                        print "Splits";
                    elif IsInert(l,OK) then
                        print "Inert";
                    else
                        print "Ramified";
                    end if;
                end if;

                Fl:=GF(l);
                Xl:=ChangeRing(X,Fl);
                El:=ChangeRing(E,Fl);
                psil:=map<Xl->El | DefiningEquations(psi) >;
                Rl:=El ! Eltseq(R);
                Ql := El ! Eltseq(Q);
                Gl:=Order(Rl);
                if VerboseLevel ge 3 then
                    print "Order Gl =", Gl;
                end if;

                ms:=[];
                for m in [0..Gl-1] do
                    D:=Decomposition(Pullback(psil,Place(m*Rl+n*Ql)));
                    if (D[1][2] eq 1) and (#D eq 1) then // point defined over F_l^2 and not F_l
                        if IsInert(l,OK) eq false then
                            continue;
                        end if;
                    elif (D[1][2] eq 1) and (#D eq 2) then // pair distinct points defined over F_l
                        if IsSplit(l,OK) eq false then
                            continue;
                        end if;
                    end if;
                    ms := ms cat [m]; // include m as a possibility mod G_l if checks passed
                end for;
                if VerboseLevel ge 3 then
                    print "Surviving ms mod Gl are:\n", ms;
                end if;

                // If we used a ramified prime with a bad Gl value and it failed,
                // then we do not include it in sieve
                // this could help avoid a potential combinatorial explosion
                if l in extra_l and ms ne [] then
                    if VerboseLevel ge 3 then
                        print "Removing l =", l;
                        print "++++++++++++++++++++++++";
                    end if;
                    continue l;
                end if;

                mls:=mls cat [*ms*];
                Gls:=Gls cat [Gl];
                i := i + 1;
                // We now apply the CRT to solve the system of linear congruences.
                if VerboseLevel ge 3 then
                    print "Carrying out CRT step";
                end if;
                if Type(Newms) eq MonStgElt then // not yet defined, so we are at first step
                    Newms:=[* [mls[1][j]] : j in [1..#mls[1]]*];
                    if VerboseLevel ge 3 then
                        print "Completed CRT,", #Newms, "possible sequences remaining";
                        print "++++++++++++++++++++++++";
                    end if;
                    if #Newms eq 0 then // If Newms is empty, no sols, so contradiction.
                        assert d notin KnownBad; // sanity check if check_bad_d = true
                        if VerboseLevel ge 1 then
                            print d, "eliminated after reaching l =", l;
                            print "++++++++++++++++++++++++++++++++++++++++++++++++";
                        end if;
                        continue d;
                    end if;
                else
                    ml := mls[i];
                    Ai:=[1 : j in [1..i]];
                    Ni:=[Gls[j] : j in [1..i]];
                    NNewms:=[* *];
                    for j in [1..#Newms] do
                        u:=[* *];
                        for m in ml do
                            w:=Newms[j] cat [m];
                            u:=u cat [*w*];
                        end for;
                        NNewms:=NNewms cat u;
                    end for;
                    Newms:=NNewms;
                    Newms:=[P : P in Newms | Solution(Ai,P,Ni) ne -1];
                    if VerboseLevel ge 3 then
                        print "Completed CRT,", #Newms, "possible sequences remaining";
                        // We then provide even more information about the possible solutions
                        if #Newms gt 0 then
                            possible_ms := Sort([Solution(Ai,P,Ni) : P in Newms | Solution(Ai,P,Ni) ne -1]);
                            lcm_Gl := LCM(Gls);
                            print "Possible values of m mod", lcm_Gl, "are:\n", possible_ms;
                            print "++++++++++++++++++++++++";
                        end if;
                    end if;
                    if #Newms eq 0 then // If Newms is empty, no sols, so contradiction.
                        if l gt max_l then
                            max_l := l;
                        end if;
                        if VerboseLevel ge 1 then
                            print d, "eliminated after reaching l =", l;
                            print "++++++++++++++++++++++++++++++++++++++++++++++++";
                        end if;
                        assert d notin KnownBad; // sanity check if check_bad_d = true
                        continue d;
                    end if;
                end if;
            end for;
            assert #Newms ne 0; // if we have reached this point then #Newms ne 0
            if VerboseLevel ge 1 then
                print d, "has not been eliminated";
            end if;
            if d in KnownBad then // used for check_bad_d = true
                if VerboseLevel ge 1 then
                    print "Expected, since it should fail";
                    print "++++++++++++++++++++++++++++++++++++++++++++++++";
                end if;
            else
                if VerboseLevel ge 1 then
                    print "Unexpected, we hoped to eliminate it";
                    print "++++++++++++++++++++++++++++++++++++++++++++++++";
                end if;
            end if;
        end for; // end of d loop
    end for; // end of n_range loop
    if VerboseLevel ge 1 then
        print "Maximum l used in sieve was l =", max_l; // (not including any ramifed primes used)
    end if;
    // We now verify that the curve X_0(N) is indeed nonsingular at each prime l we used in the sieve
    // We include all primes that divide elements of range_d to ensure any ramified primes that were used are checked too
    primes_to_check := {l : l in ls | l le max_l + 1};
    ds_used := [d : d in range_d | d ne 0 and d ne 1 and IsSquarefree(d)];
    extra_to_check := {l : l in &join{Set(PrimeFactors(d)) : d in ds_used} | IsZero((2*N) mod l) eq false};
    primes_to_check := primes_to_check join extra_to_check;
    if VerboseLevel ge 3 then
        print "We verify nonsingularity for l in:\n", primes_to_check;
    end if;
    for l in primes_to_check do
        assert is_nonsing_mod_l(X,N,cusp,l);
    end for;
    return failed_d, KnownBad;
end function;

/////////////////////////////////////////
/////////////////////////////////////////

// We run the sieve for each value of N
// We first run the sieve with VerboseLevel 0
// The output is both at the end of this file
// and in the bielliptic_sieve_output.txt file

for N in [53,61,79,83,89,101,131,65] do
    time failed_d, KnownBad := sieve(N);
    assert failed_d eq {};
    print "Bad d for N =", N, "are:", KnownBad;
    print ">>>>>>>>>>>>>>>>>>>>>>>>";
end for;

////////////////////////////////////////////////////////////////////////////

// We now run the sieve with VerboseLevel 2
// The output is in the bielliptic_sieve_output.txt file

for N in [53,61,79,83,89,101,131,65] do
    sieve(N : VerboseLevel := 2, check_bad_d := true);
    print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>";
    print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>";
end for;

////////////////////////////////////////////////////////////////////////////

// Code to reproduce the example computations
// The output is in the bielliptic_sieve_output.txt file

sieve(53: VerboseLevel := 3, check_bad_d := true, range_d := [-47, 3, -11]);

/* Output for VerboseLevel 0 loop:
N = 53
Time: 205.850
Bad d for N = 53 are: { -43, -11, -7, -1 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 61
Time: 131.990
Bad d for N = 61 are: { -19, -3, -1, 61 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 79
Time: 393.710
Bad d for N = 79 are: { -43, -7, -3 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 83
Time: 316.200
Bad d for N = 83 are: { -67, -43, -19, -2 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 89
Time: 153.100
Bad d for N = 89 are: { -67, -11, -2, -1, 89 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 101
Time: 405.750
Bad d for N = 101 are: { -43, -19, -1 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 131
Time: 749.500
Bad d for N = 131 are: { -67, -19, -2 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 65
Time: 143.290
Bad d for N = 65 are: { -79, -1 }
>>>>>>>>>>>>>>>>>>>>>>>>
*/
