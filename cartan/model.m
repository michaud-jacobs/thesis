// Magma code to support the computations in my PhD thesis.

// The code in this file obtains a new model for the curve X_ns(13)
// together with equations for the modular involution and quotient map.
// We also test nonsingularity at the required primes and verify the rank of J_ns(13)(Q).

// The code uses data from the file "eqn_data.m" available at:
// https://github.com/michaud-jacobs/thesis/blob/main/cartan/eqn_data.m

// The new model for X_ns(13) obtained using this code is also available in the "eqn_data.m" file.

load "eqn_data.m";

////////////////////////////////////////////

old_X := Curve(ProjectiveSpace(R), old_eqns);  // The curve X_ns(13)

X_plus := Curve(ProjectiveSpace(S), eqn_X_plus); // The curve X_ns+(13),

old_rho :=map < old_X -> X_plus | old_rho_eqns >; // Quotient map

// We define the seven known rational points on the quotient curve X_ns+(13)
SvnPts := [X_plus ! [0,1,0], X_plus ! [0,0,1], X_plus ! [-1,0,1], X_plus ! [1,0,0], X_plus ! [1,1,0], X_plus ! [0,3,2], X_plus ! [1,0,1]];

////////////////////////////////////////////

// We compute the pullbacks of the seven rational points on X_ns+(13)

// We first compute the fields of definition and some pullback schemes

Ds := []; // form list of pullback schemes of points
ds := {}; // form list of quadratic field discriminants
for pt in SvnPts do
    S := Pullback(old_rho, pt); // Pullback scheme including base scheme
    BS := BaseScheme(old_rho);
    D := Difference(S, BS);  // Pullback scheme withoout base scheme
    Ds := Ds cat [D];
    pb, K1 := PointsOverSplittingField(D);
    K2 := NumberField(AbsolutePolynomial(K1));
    d := Squarefree(Discriminant(Integers(K2)));
    ds := ds join {d};
end for;

// We now find the equations of the modular involution
// We do this by seeing which maps interchange the pairs of quadratic points obtained above

T<x> := PolynomialRing(Rationals());   // Setting up a more general field that contains all the square roots we need
ds := { -163, -67, -19, -11, -7, -2 };
QQ := ext<Rationals() | [x^2 -d : d in ds] >;
PQ := AmbientSpace(old_X);
PQQ := BaseChange(PQ,QQ);

quad_pts1 := [ ];
quad_pts2 := [ ];

for D in Ds do
    pair := Points(Intersection(PQ,D),QQ);
    quad_pts1 := quad_pts1 cat [PQQ ! Eltseq(pair[1])];
    quad_pts2 := quad_pts2 cat [PQQ ! Eltseq(pair[2])];
end for;

T1 := TranslationOfSimplex(PQQ,quad_pts1 cat [quad_pts2[1],quad_pts2[2]]);
T2 := TranslationOfSimplex(PQQ,quad_pts2 cat [quad_pts1[1],quad_pts1[2]]);
TofS := T2^(-1)*T1;
EqTS:=DefiningEquations(TofS);

w_old := map< old_X -> old_X | EqTS>;  // The modular involution on the curve
Mw:=Transpose((Matrix(w_old)));        // Matrix of the modular involution

// We now diagonalise the matrix.
// The following matrix was obtained from Magma's inbuilt function "PrimaryRationalForm"
// We input the matrix directly here since each call of "PrimaryRationalForm" can pick a different diagonalising matrix
// The following ensures the equations we end up with are always the same.

TZ := Matrix( [
[ 0, 0, 0, 1,-1, 0, 0, 0],
[ 1, 0, 0, 0, 0, 0, 0, 0],
[ 0, 1, 0, 0, 0, 0, 0, 0],
[ 1, 0, 0, 0, 0, 0, 0,-2],
[ 1,-1,-2, 0, 0, 0, 0, 0],
[ 1, 0, 0, 0, 0,-2, 0, 0],
[ 0, 1, 0, 0, 0, 0,-2, 0],
[ 0, 0, 0, 1, 1, 0, 0, 0]
]);

T := ChangeRing(TZ,Rationals());

Diag := DiagonalMatrix([1,1,1,-1,-1,-1,-1,-1]);
assert T*Mw*(T^-1) eq Diag;

Eqg := [&+[(T^-1)[i][j]*R.j : j in [1..8]] : i in [1..8]]; // We use T^-1 to find our change of coordinate map
g:=hom<R->R | Eqg>;                   // Change of coordinate map

////////////////////////////////////////////

// Apply our change of coordinates to obtain new equations
// Multiply by 4 to clear denominators

Neqns := [4*g(ee) : ee in old_eqns];
assert Neqns eq new_eqns; // Matches data file.

// Apply change of coordinates to obtain new equations for map (to same bottom curve)

Nrhos := [g(ee) : ee in old_rho_eqns];
assert Nrhos eq new_rho_eqns; // Matches data file.

// We now have the following new data:

X:= Curve(ProjectiveSpace(R),new_eqns);            // New model of our curve X_ns(13)
w:= map<X -> X | [Diag[i][i]*R.i : i in [1..8]]>;  // New modular involution on X_ns(13)
rho := map< X -> X_plus | new_rho_eqns >;          // New equations for the quotient map from X_ns(13) to X_ns+(13)


////////////////////////////////////////////////////////////////////////////////

// Check that this new model is nonsingular at the primes used in the sieve
// Runtime: This takes a bit under an hour per prime on average
// An alternative would be to use the method employed in the code of Chapter 4
// See the "is_nonsing_mod_l" function in the file "bielliptic_models.m", available at:
// https://github.com/michaud-jacobs/thesis/blob/main/bielliptic/bielliptic_models.m

for p in [3,5,31,43,53,61,73] do
    print "Starting nonsingularity check for p =", p;
    Xp:=ChangeRing(X,GF(p));
    assert IsNonsingular(Xp);
end for;

////////////////////////////////////////////////////////////////////////////////

// We verify that J_(ns)(13)(Q) has rank 3
// We must verify that J_0^-(169)(Q) has rank 0

J := JZero(169);
Jmin := Image(1-AtkinLehnerOperator(J,169)); // This is J_0^-(169)
dec := Decomposition(Jmin);
assert #dec eq 2; // 2 abelian varieties in the decomposition
assert IsZeroAt(LSeries(dec[1]),1) eq false; // implies rank 0
assert IsZeroAt(LSeries(dec[2]),1) eq false; // implies rank 0
// So J_0^-(169)(Q) has rank 0
