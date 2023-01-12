sieve := function(N: VerboseLevel := 0 );
    print "N =", N;
    X, E, psi, B, w := model_and_map(N);
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
        Q := mu(0*M.1);
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
        n_range := [0,1];
    end if;

    initial_ls := [l : l in PrimesInInterval(3,1000) | IsZero(N mod l) eq false];
    ls := [];
    for l in initial_ls do
        Fl := GF(l);
        El:=ChangeRing(E,Fl);
        Rl:=El ! Eltseq(R);
        Nl:=Order(Rl);
        if Max(PrimeFactors(Nl)) le 7 then
            ls := ls cat [l];
        end if;
    end for;
    if VerboseLevel ge 1 then
       print "Primes l to use in sieve are:\n", ls;
       print "++++++++++++++++++++++++";
    end if;

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
        for t in [-10..10]  do
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

        for d in [d : d in [-100..100] | d ne 0 and d ne 1 and IsSquarefree(d)] do
            if VerboseLevel ge 1 then
                print "Considering d =", d;
            end if;

            if d in KnownBad then
                if VerboseLevel ge 1 then
                    print d, "is known to fail";
                    print "++++++++++++++++++++++++++++++++++++++++++++++++";
                end if;
                continue;
            end if;

            K := QuadraticField(d);
            OK := Integers(K);

            mls:=[* *];
            Nls:=[];
            if VerboseLevel ge 3 then
                print "Starting sieve";
            end if;
            i := 0;
            for l in ls do
                if VerboseLevel ge 3 then
                    print "Using l =", l;
                end if;
                i := i + 1;
                Fl:=GF(l);
                Xl:=ChangeRing(X,Fl);
                El:=ChangeRing(E,Fl);
                psil:=map<Xl->El | DefiningEquations(psi) >;
                Rl:=El ! Eltseq(R);
                Ql := El ! Eltseq(Q);
                Nl:=Order(Rl);
                if VerboseLevel ge 3 then
                    print "Order Nl =", Nl;
                end if;
                Nls:=Nls cat [Nl];
                ms:=[];
                for m in [0..Nl-1] do
                    D:=Decomposition(Pullback(psil,Place(m*Rl+n*Ql)));
                    if (D[1][2] eq 1) and (#D eq 1) then // point defined over extension of Fl
                        if IsInert(l,OK) eq false then
                            continue;
                        end if;
                    else
                        P :=Eltseq(RepresentativePoint(D[1][1]));
                            if IsInert(l,OK) and P[1] ne 0 then
                                continue;
                            end if;
                    end if;
                    ms := ms cat [m];
                end for;
                if VerboseLevel ge 3 then
                    print "Surviving ms mod Nl are:\n", ms;
                end if;
                mls:=mls cat [*ms*];

                if VerboseLevel ge 3 then
                    print "Carrying out CRT step";
                end if;
                if l eq ls[1] then
                    Newms:=[* [mls[1][j]] : j in [1..#mls[1]]*];
                    if VerboseLevel ge 3 then
                        print "Completed CRT,", #Newms, "possible sequences remaining";
                        print "++++++++++++++++++++++++";
                    end if;
                    if #Newms eq 0 then // If Newms is empty, then we have a contradiction.
                        if VerboseLevel ge 1 then
                            print d, "eliminated after reaching l =", l;
                            print "++++++++++++++++++++++++++++++++++++++++++++++++";
                        end if;
                    end if;
                else
                    ml := mls[i];
                    Ai:=[1 : j in [1..i]];
                    Ni:=[Nls[j] : j in [1..i]];
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
                        print "++++++++++++++++++++++++";
                    end if;
                    if #Newms eq 0 then // If Newms is empty, then contradiction.
                        if VerboseLevel ge 1 then
                            print d, "eliminated after reaching l =", l;
                            print "++++++++++++++++++++++++++++++++++++++++++++++++";
                        end if;
                        assert d notin KnownBad; // sanity check when testing all d
                        break;
                    end if;
                end if;
            end for;
            if #Newms ne 0 then
                if VerboseLevel ge 1 then
                    print d, "has not been eliminated";
                end if;
                if d in KnownBad then
                    if VerboseLevel ge 1 then
                        print "Expected, since it should fail";
                        print "++++++++++++++++++++++++++++++++++++++++++++++++";
                    end if;
                else
                    if VerboseLevel ge 1 then
                        print "Unexpected, we hoped to eliminate it";
                        print "++++++++++++++++++++++++++++++++++++++++++++++++";
                    end if;
                    failed_d := failed_d join {d};
                end if;
            end if;
        end for;
    end for;
    return failed_d, KnownBad;
end function;

/////////////////////////////////////////
/////////////////////////////////////////

// We run the sieve for each value of N
// We first run the sieve with VerboseLevel 0
// The output is both at the end of this file
// and in the output file

for N in [53,61,79,83,89,101,131,65] do
    time failed_d, KnownBad := sieve(N);
    assert failed_d eq {};
    print "Bad d for N =", N, "are:", KnownBad;
    print ">>>>>>>>>>>>>>>>>>>>>>>>";
end for;

// We now run the sieve with VerboseLevel 2
// The output is in the bielliptic_sieve_output.txt file

for N in [53,61,79,83,89,101,131,65] do
    sieve(N : VerboseLevel := 2);
    print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>";
    print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>";
end for;


/* Output for VerboseLevel 0 loop:
N = 53
Time: 860.410
Bad d for N = 53 are: { -43, -11, -7, -1 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 61
Time: 989.410
Bad d for N = 61 are: { -19, -3, -1, 61 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 79
Time: 941.520
Bad d for N = 79 are: { -43, -7, -3 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 83
Time: 803.400
Bad d for N = 83 are: { -67, -43, -19, -2 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 89
Time: 609.800
Bad d for N = 89 are: { -67, -11, -2, -1, 89 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 101
Time: 1177.780
Bad d for N = 101 are: { -43, -19, -1 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 131
Time: 1761.650
Bad d for N = 131 are: { -67, -19, -2 }
>>>>>>>>>>>>>>>>>>>>>>>>
N = 65
Time: 516.920
Bad d for N = 65 are: { -79, -1 }
>>>>>>>>>>>>>>>>>>>>>>>>
*/
