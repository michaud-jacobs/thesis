N := 65;
X, ws, pair := eqs_quos(p,[[p]]);
E := pair[1][1];
psi := pair[1][2];
M, mu, muinv := MordellWeilGroup(E);
R := mu(M.1);
Rseq := Eltseq(R);

KnownBad := {};
for m in [-10..10]  do
    dec := Decomposition(Pullback(psi,Place(m*R)));
    d := Discriminant(Integers(ResidueClassField(dec[1][1])));
    if IsZero(d mod 4) then
        d := Integers() ! (d/4);
    end if;
    if d ne 1and AbsoluteValue(d) lt 100 then
        KnownBad := KnownBad join {d};
    end if;
end for;


test_ls := [l : l in PrimesInInterval(3,1000) | l ne p];
ls := [];
for l in test_ls do
    Fl := GF(l);
    El:=ChangeRing(E,Fl);
    Rl:=El ! Rseq;  // [1,0,1] Generates E(Q)
    Nl:=Order(Rl);
    if Max(PrimeFactors(Nl)) le 7 then
        ls := ls cat [l];
    end if;
end for;

for d in [d : d in [-100..100] | d ne 0 and d ne 1 and IsSquarefree(d)] do

K := QuadraticField(d);
OK := Integers(K);

mls:=[* *];
Nls:=[];

i := 0;
for l in ls do
    i := i + 1;
    Fl:=GF(l);
    Xl:=ChangeRing(X,Fl);
    El:=ChangeRing(E,Fl);
    psil:=map<Xl->El | DefiningEquations(psi) >;
    Rl:=El ! Rseq;  // [1,0,1] Generates E(Q)
    Nl:=Order(Rl);     // Order modulo l
    Nls:=Nls cat [Nl];
    ms:=[];
    for m in [0..Nl-1] do
        D:=Decomposition(Pullback(psil,Place(m*Rl)));
        if (D[1][2] eq 1) and (#D eq 1) then // point defined over extension of Fl
            if IsInert(l,OK) eq false then
                continue;
            end if;
        end if;
        if ((D[1][2] eq 1) and (#D eq 2)) or (D[1][2] eq 2)  then // pair of distinct points over Fl or a double point over Fl
            P :=Eltseq(RepresentativePoint(D[1][1]));
            if IsInert(l,OK) and P[1] ne 0 then
                continue;
            end if;
        end if;
        ms := ms cat [m];
    end for;
    mls:=mls cat [*ms*];


// Now carry out CRT steps (within sieve)

    if l eq ls[1] then
        Newms:=[* [mls[1][j]] : j in [1..#mls[1]]*];
        if #Newms eq 0 then // If Newms is empty, then we have a contradiction.
            print d, "yes";
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
        if #Newms eq 0 then // If Newms is empty, then we have a contradiction.
            print d, "yes", l;
            assert d notin KnownBad;
            break;
        end if;
    end if;
end for;
if #Newms ne 0 then
    print d, "no >>>>>>>>>>>>>>", #Newms;
    if d in KnownBad then
        print "KnownBad";
    else print "But not KnownBad";
    end if;
end if;
end for;
