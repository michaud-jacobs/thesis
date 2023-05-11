// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.26-10

// The code carries out the irreducibility checks for signature (2m, 2l, 17)

// The output is contained within the file

////////////////////////////////////////////

// We start with the modular curve verifications
// We start by setting up the field extensions

p:=17;
L<a>:=CyclotomicField(p);
K<w>:=sub< L | a+a^-1 >; // maximal totally real subfield
assert Degree(K) eq (p-1)/2;
OK:=Integers(K);

K4<c>:=sub< L | a+a^(3^4)+a^(3^8)+a^(3^12)>; // the unique subfield of K of degree 4.
assert Degree(K4) eq (p-1)/4;

F<b>:=QuadraticField(17);
assert IsSubfield(F,K4);

d:=Discriminant(MinimalPolynomial(w,K4));
S<Z>:=PolynomialRing(K4);
assert IsIsomorphic(K, ext<K4 | Z^2-d>);  // verification that K = K4(\sqrt(d))

/////////////////////////////////////////////////////////////////////////////////

// Parts (i) and (ii)

// we first verify that for XX = X_0(14) and XX = X_0(11)
// we have XX(K4) = XX(Q(sqrt(17))).

for n in [14,11] do
    XX := SmallModularCurve(n);  // the curve X_0(N)
    rank_XX, tf := Rank(XX);
    assert rank_XX eq 0 and tf; // rank is 0, provably correct
    XXK4 := ChangeRing(XX,K4);
    M,pi,tf1,tf2 := MordellWeilGroup(XXK4);
    assert tf1 and tf2; // provably correct
    assert IsIsomorphic(TorsionSubgroup(XXK4),TorsionSubgroup(XX));
    gen:= pi(M.2);  // generator for free part
    for i in [1,2,3] do
        assert Degree(MinimalPolynomial(gen[i],F)) eq 1;  // so point is defined over F
    end for;
end for;

/////////////////////////////////////////////////////////////////////////////////

// Part (iii)
// We now carry out the checks for X = X_0(20)
// We verify that X(K) = X(Q(sqrt(17)))

X:=SmallModularCurve(20);
XK:=ChangeRing(X,K);
XK4:=ChangeRing(X,K4);
XF:=ChangeRing(X,F);

MordellWeilGroup(X);  // Z/6Z (true true)
MF,piF,tf1,tf2:=MordellWeilGroup(XF);  // Z/6Z + Z (true true)
assert tf1 and tf2; // provably correct
MW,pi,tf1,tf2:=MordellWeilGroup(XK4);  // Z/6Z + Z  (true true), about 1 minute
assert tf1 and tf2; // provably correct
R:= XK ! pi(MW.2);
Q:= XK ! pi(MW.1);

assert (XK4 ! piF(-MF.2-2*MF.1)) eq pi(MW.2); // generator of free part of XK4 comes from point in X(F), so XK4 = XF.

TorsXK:=TorsionSubgroup(XK); // Z/6Z

XdK4:=QuadraticTwist(XK4,d);
XdK:=ChangeRing(XdK4,K);

time Md,pid,tf1,tf2:=MordellWeilGroup(XdK4); // Z/2Z (true true), about 90 seconds
assert tf1 and tf2; // provably correct

// We now verify 2-divisibility

qq:=137;

q:=Factorisation(qq*OK)[1][1];
unif:=UniformizingElement(q);
Fq:=ResidueClassField(q);
Xq:=ChangeRing(XK,Fq);
Ab:=AbelianGroup(Xq);         // this is Z/2Z + Z/60Z

for b in [0,1] do
    Pt:=R+b*Q;
    m:=Minimum([Valuation(a,q) : a in Eltseq(Pt) | not a eq 0]); // we reduce the point 
    Red1:=[unif^(-m)*a : a in Eltseq(Pt)];
    Red:=Xq![Evaluate(a,Place(q)) : a in Red1];   // reduction of Pt
    Order(Red);              // orders are 60, 60
end for;

/////////////////////////////////////////////////////////////////////////////////

// Part (iv)
// Finally we carry out the checks for the elliptic curve 52a1.

C := EllipticCurve([0, 0, 0, 1, -10]);
assert Conductor(C) eq 52;
CremonaReference(C); // 52a1
CK4 := ChangeRing(C,K4);
CdK4 := QuadraticTwist(CK4,d);

Rank(CK4);  // 0 true
Rank(CdK4); // 0 true
TorsionSubgroup(ChangeRing(C,K)); // Z/2Z

assert ModularDegree(C) eq 3;

/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

// We now carry out the remaining irreducibility checks.
// We first check the j-invariant cannot be in Q(sqrt(17))
// by considering its reduction mod a prime of K above 2

p:=17;
L<zet>:=CyclotomicField(p);
K:=sub<L | zet+1/zet>; // Q(zeta_p)^+.
OK:=Integers(K);

thj:=OK!(zet+1/zet);      // j = 1
thk:=OK!(zet^4+1/zet^4);  // k = 4

F<b>:=QuadraticField(17);
assert IsSubfield(F,K);
OF := Integers(F);

assert #Factorisation(2*OF) eq 2; // so quotient is F_2

qq := Factorisation(2*OK)[1][1]; // one of the two primes of K above 2
Fqq<t>, pi := ResidueClassField(qq);  // finite field of size 2^4

expr := ((thj^2)*(thk)^2) / (thj-thk)^2;
red := pi(expr); // reduction of expr
assert Degree(MinimalPolynomial(red)) eq 2;  // so not defined over F2.

/////////////////////////////////////////////////////////////////////////////////

// We now verify there exists a curve with a 2l torsion point in each case. We follow
// S. Anni and S. Siksek. Modular elliptic curves over real abelian fields and the generalized Fermat equation x^2l+y^2m=z^p.
// Algebra Number Theory 10(6):1147--1172, 2016.
// This is the code of Anni and Siksek (very slightly adapted).

for i in [1,2] do // i = 1 is case 1, i = 2 is case 2.
    print "Doing case", i;
    p:=17;
    L<zet>:=CyclotomicField(p);
    K<th>:=sub<L | zet+1/zet>;

    if i eq 2 then
       K:=Subfields(K,4)[1,1];
    end if;

    OK:=MaximalOrder(K);
    assert NarrowClassNumber(K) eq 1; // required condition to apply the method
    U,phi:=UnitGroup(K);
    // We will determine a system of totally positive units.
    V:=U;
    A:=AbelianGroup([2]);
    for i in [1..Degree(K)] do
    	img:=[];
    	for u in OrderedGenerators(U) do
    		if RealEmbeddings(phi(u))[i] gt 0 then
    		   Append(~img,A!0);
    		else
    		   Append(~img,A!1);
    		end if;
    	end for;
    	psi:=hom<U->A | img>;
    	V:=V meet Kernel(psi);
    end for;
    posunits:=[phi(U!v) : v in OrderedGenerators(V)];
    assert &and[IsTotallyPositive(u) : u in posunits];
    assert &and[Norm(u) eq 1 : u in posunits];
    print "The following is our system of totally positive units",
    [K!u : u in posunits];
    G,S,mu:=AutomorphismGroup(K);
    subG:=[D`subgroup : D in Subgroups(G)];
    BSet:={};
    for D in subG do   // D is a subgroup of the Galois group.
    	T,pi:=quo<G|D>; // T is the cosets of G/D.
    	for Tp in Subsets({q : q in T}) do // Tp is T^prime
    					// in the notation of the paper [1].
    		if #Tp ne 0 and #Tp ne #T then
    				// We check that Tp is non-empty and proper.
    		   TpD:=[mu(t@@pi) : t in Tp];
    				// TpD is the set of products
    				// sigma tau
    				// where sigma is in D
    				// tau is in T^prime.
    		   BTpD:=GCD( [ Integers()!Norm(&*[u@t : t in TpD]-1)  : u in posunits  ]  );
    				// This B_{T^prime,D}(u_1,...,u_d) in the
    				// notation of the paper [1].
    		   BSet:=BSet join {BTpD};
    		end if;
    	end for;
    end for;
    print "The set of B_{T^prime,D}(u_1,...,u_d) is ", BSet;
    lset:=&cat[PrimeDivisors(B) : B in BSet];
    lset:=[l : l in lset | l ge 5];  // We're only interested in ell >= 5.
    print "The set of surviving primes ell is", lset;
    print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

/* Output
Doing case 1
The following is our system of totally positive units [
    th^2 + 2*th + 1,
    th^7 + 2*th^6 - 4*th^5 - 8*th^4 + 4*th^3 + 8*th^2,
    th^7 - 7*th^5 + 14*th^3 - 7*th + 2,
    th^6 - 6*th^4 + 9*th^2,
    th + 2,
    th^4 - 4*th^2 + 4,
    3*th^7 + 6*th^6 - 16*th^5 - 34*th^4 + 16*th^3 + 47*th^2 + 11*th - 3
]
The set of B_{T^prime,D}(u_1,...,u_d) is  { 1, 16777216 }
The set of surviving primes ell is []
"+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++"
Doing case 2
The following is our system of totally positive units [
    1/2*(-K.1^3 + 10*K.1 + 5),
    K.1^2,
    1/2*(5*K.1^3 + 14*K.1^2 - 2*K.1 - 1)
]
The set of B_{T^prime,D}(u_1,...,u_d) is  { 1, 4096 }
The set of surviving primes ell is []
*/
