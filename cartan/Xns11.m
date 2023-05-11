// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.27-7

// We verify some basic computations for the curve X_ns(11)
// We check that the points at infinity on our affine model consist of a pair of quadratic points
// which arise as the pullback of the identity point on X_ns+(11)

// We also check that H(Q) is empty.

////////////////////////////////////////////

A<x,y,t> := AffineSpace(Rationals(),3);
eqns := [y^2+y-(x^3-x^2-7*x+10), t^2 +4*x^3+7*x^2-6*x+19];
X := Curve(A,eqns); // The affine model used for X_ns(11)

E := EllipticCurve([0,-1,+1,-7,10]); // The curve X_ns+(11)
// Elliptic Curve defined by y^2 + y = x^3 - x^2 - 7*x + 10 over Rational Field

assert Conductor(E) eq 121;
MW,_,tf1,tf2 := MordellWeilGroup(E);
assert tf1 and tf2;  // MordellWeil group has been provably computed
assert MW eq AbelianGroup([0]); // E(Q) is isomorphic to Z

rho := map<X -> E | [x,y,1]>; // degeneracy map

// We wish to verify that there is a pair of quadratic points at infinity
// and that these arise as the pullback of the identity on E

PX := ProjectiveClosure(X);
P<xx,yy,zz,tt> := AmbientSpace(PX);
assert AffinePatch(PX,1) eq X;
H := HyperplaneAtInfinity(A);

inf_scheme := H meet PX;   // Scheme defining points at infinity on X
PointsOverSplittingField(inf_scheme);

/*
{@ (0 : r1 : 1 : 0), (0 : r2 : 1 : 0) @}
Algebraically closed field with 2 variables over Rational Field
Defining relations:
[
    r2^2 + 1/4,
    r1^2 + 1/4
]
*/

// We see that the points are defined over K = Q(sqrt(-1))

K<a>:= QuadraticField(-1);
inf_scheme_K := BaseChange(inf_scheme,K);
Points(inf_scheme_K);
// {@ (0 : -1/2*a : 1 : 0), (0 : 1/2*a : 1 : 0) @}

assert HasPointsOverExtension(inf_scheme_K) eq false; // There are no further points

rhoP := map<PX -> E | [xx,yy,tt]>; // degenracy map from projective closure to E
assert Degree(rhoP) eq 2; // This is indeed the correct map
pullback_scheme := Pullback(rhoP,Identity(E)); 
Points(pullback_scheme,K); // We see that we have the same points:
// {@ (0 : -1/2*a : 1 : 0), (0 : 1/2*a : 1 : 0) @}

////////////////////////////////////////////

// We check that H(Q) is empty using the TwoCoverDescent function

QQ<s> := PolynomialRing(Rationals());
H := HyperellipticCurve(-(2*s^3-4*s^2-28*s+41)*(4*s^3+7*s^2-6*s+19));
assert TwoCoverDescent(H) eq {}; // takes about 5 minutes
