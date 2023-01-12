// Note: can use formal immersion or primes of mult reduction in sieve for Frey curve in FLT paper

R<x,y,z,t>:=PolynomialRing(Rationals(),4);
eqns :=  [4*y^2 + 4*x*z - z^2 + t^2, 4*x^3 - 4*x^2*y + 8*x^2*z + 4*x*y*z - 7*x*z^2 - 4*y*z^2 + z^3 + 3*x*t^2 - z*t^2];
X:=Curve(ProjectiveSpace(R),eqns);
w:=iso<X -> X | [x,y,z,-t], [x,y,z,-t]>;
S<r,s,u>:=PolynomialRing(Rationals(),3);
G:= r^3 - r^2*s - 3*r*s^2 - r^2*u + r*s*u + s^2*u - s*u^2;
C:= Curve(ProjectiveSpace(S), [G]);
rho:=map<X -> C | [x,y,z]>;
EC,mu:= EllipticCurve(C, C ! [0,1,0]);
E,pi:= SimplifiedModel(EC);
psi:=Expand(rho*mu*pi);
assert Degree(psi) eq 2;
// Divide out by factor of 9 in all equations, to allow reduction mod 3
psi := map<X -> E | [ee / 9 : ee in DefiningEquations(psi)]>;

test_ls := [l : l in PrimesInInterval(3,1000) | l ne 61];
all_ls := [];
for l in test_ls do
    Fl := GF(l);
    El:=ChangeRing(E,Fl);
    Rl:=El ! [1,0,1];  // [1,0,1] Generates E(Q)
    Nl:=Order(Rl);
    if Max(PrimeFactors(Nl)) le 7 then
        all_ls := all_ls cat [l];
    end if;
end for;

for d in [d : d in [-100..100] | d ne 0 and d ne 1 and IsSquarefree(d)] do


//F:= -4*y^2 - 4*x*z + z^2;

ls := [l : l in all_ls | (d mod l) ne 0];

K := QuadraticField(d);
OK := Integers(K);

mls:=[* *];
Nls:=[];

i := 0;
for l in ls do
    i := i + 1;
    Fl:=GF(l);
    S<b> := PolynomialRing(Fl);
    // We reduce the curves mod l.
    Xl:=ChangeRing(X,Fl);
    El:=ChangeRing(E,Fl);
    psil:=map<Xl->El | DefiningEquations(psi) >;
    Rl:=El ! [1,0,1];  // [1,0,1] Generates E(Q)
    Nl:=Order(Rl);     // Order modulo l
    Nls:=Nls cat [Nl];
    ms:=[];
    for m in [0..Nl-1] do
        D:=Decomposition(Pullback(psil,Place(m*Rl)));
        if (D[1][2] eq 1) and (#D eq 1) then // point defined over extension of Fl
            if IsSplit(l,OK) then
                continue;
            end if;
        end if;
        if ((D[1][2] eq 1) and (#D eq 2)) or (D[1][2] eq 2)  then // pair of distinct points over Fl or a double point over Fl
            P :=Eltseq(RepresentativePoint(D[1][1]));
            if IsInert(l,OK) and P[4] ne 0 then
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
            break;
        end if;
    end if;
end for;
if #Newms ne 0 then print d, "no >>>>>>>>>>>>>>", #Newms; end if;

end for;




// for -199 and ls < 200
// for i in [1..9] do Solution([1 : j in [1..17]],Newms[i],Nls); end for;


/*
R := E ! [1,0,1];
for m in [-10..10]  do 
    dec := Decomposition(Pullback(psi,Place(m*R)));
    <m,Discriminant(Integers(ResidueClassField(dec[1][1])))>;
end for;
*/
/*
<-10, -38539698755581703>
<-9, -20302210497651>
<-8, -44830186756>
<-7, -12636502971>
<-6, -96127>
<-5, -879499>
<-4, -6527>
<-3, 61>
<-2, -727>
<-1, -3>
<0, -4>
<1, -19>
<2, 1>
<3, -3>
<4, -4>
<5, -3>
<6, -199>
<7, -163>
<8, -1028>
<9, -500811>
<10, -1951>
*/


// can use twist_check too

/*
p := 61;
for d in [d : d in [-200..200] | d ne 0 and d ne 1 and IsSquarefree(d)] do
    <d,twist_check(d,p)>;
end for;
*/






// The all -3s answer, the final one in that case
// [-Nls[i] + Newms[36][i] : i in [1..#Nls]];





// Expanded twist check using B = j(O).
// Compute using HilbertClassPolynomial, see https://math.mit.edu/classes/18.783/2017/LectureNotes21.pdf
// B depends only on p, so should not be recomputed every time.

twist_check_new := function(d,p);
    pass := 0;
    K := QuadraticField(d);
    OK := Integers(K);
    DOK := Discriminant(OK);

    M := QuadraticField(-p);
    OM := Integers(M);
    DOM := Discriminant(OM);

    ls := [l : l in PrimeFactors(DOK) | IsZero(DOM mod l) eq false];
    for l in ls do
        ll := Factorisation(l*OM)[1][1];
        if IsPrincipal(ll) eq false then
            pass := 1;
            return pass;
        end if;
    end for;
    D := Discriminant(EquationOrder(M));
    B := NumberField(HilbertClassPolynomial(D));
    OB := Integers(B);
    for l in ls do
        fac := Factorisation(l*OB);
        norms_l := [Norm(ll[1]) : ll in fac ];
        if l notin norms_l then
            pass := 2;
            return pass;
        end if;
    end for;
    return pass;
end function;

/*
p := 61;
for d in [d : d in [-100..100] | d ne 0 and d ne 1 and IsSquarefree(d)] do
    <d,twist_check_new(d,p)>;
end for;
*/

/* Can use this for Hasse principle violation:
** might be a smaller d now that twist check has been adapted **
* Maybe easier to use 97 as it is prime, and same checks seem to hold *
let d = 57, K = Q(root d), only primes that ramify are 3 and 19.
the the twist check theorem fails, so X0(61)^57 has points locally at 3 and 19.
for the other primes we use theorem 1.1,
-- if l splits in K we have a local point
-- if l is inert in K and does not divide 61 (i.e. ne 61) we have a local point
-- the prime l = 61 splits in K, so we are covered by the first case
So we have points everywhere locally, but no global point by the the sieve, violation of Hasse
See paper for how this might be due to Brauer Manin obstruction.
*/




/*
// Checking local points directly at 97 twist
R<x,y,z,t> := PolynomialRing(Rationals(),4);
eq1 := 4*x*z + 4*y^2 - z^2 + 97*t^2;
eq2 := 4*x^3 - 4*x^2*y + 8*x^2*z + 4*x*y*z - 7*x*z^2 + 3*x*61*t^2 - 4*y*z^2 + z^3 - z*61*t^2;
Xd := Curve(ProjectiveSpace(R),[eq1,eq2]);
X97 := ChangeRing(Xd,GF(97));
Points(X97); // Plenty of points
*/
