// Magma code to support the computations in my PhD thesis.

// The code in this file contains code for computing models of certain curves

////////////////////////////////////////////

// This function takes as input a basis, B, of cuspforms at level N
// If X_0(N) can be canonically embedded, it computes a model for X_0(N)
// The function is based on the code of Ozman and Siksek in their paper 'Quadratic Points on Modular Curves'

canonic := function(B);
    N := Level(B[1]);
    prec := 5*N;  // precision to be used, can be increased
    dim:=#B;
    L<q>:=LaurentSeriesRing(Rationals(),prec);
    R<[x]>:=PolynomialRing(Rationals(),dim);
    Bexp:=[L!qExpansion(B[i],prec) : i in [1..dim]]; // q expansions of cusp forms
    eqns:=[R | ];
    d:=1;
    tf:=false;
    while tf eq false do   // We search for degree d relations
	d:=d+1;
	mons:=MonomialsOfDegree(R,d);
	monsq:=[Evaluate(mon,Bexp) : mon in mons];
	V:=VectorSpace(Rationals(),#mons);
	W:=VectorSpace(Rationals(),prec-10);
	h:=hom<V->W | [W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]]>;
	K:=Kernel(h);
	eqns:=eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
        I:=Radical(ideal<R | eqns>);
	X:=Scheme(ProjectiveSpace(R),I);
	if Dimension(X) eq 1 then
	    if IsIrreducible(X) then
		X:=Curve(ProjectiveSpace(R),eqns);
		if Genus(X) eq dim then
		    tf:=true;
		end if;
	    end if;
	end if;
    end while;

    eqns := [LCM([Denominator(c) : c in Coefficients(eqn)])*eqn : eqn in eqns]; // scale equations
    X := Curve(ProjectiveSpace(R),eqns); // same curve with scaled equations

    // We now check relations up to the Sturm bound

    indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];
    indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)

    for eqn in eqns do
	wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
	hecke:=Ceiling(indexGam*wt/12);  // Sturm bound for Gamma_0(N)
	Bexp1:=[qExpansion(B[i],hecke+10) : i in [1..dim]]; // q-expansions
	assert Valuation(Evaluate(eqn,Bexp1)) gt hecke+1;
    end for; // We have now checked the correctness of the equations for X.

 return(X);
end function;

////////////////////////////////////////////

// This function takes as input a level N
// It returns a basis of cusp forms for S_2(N) and the matrix of the AL involution w_N
// such that w_N acts diagonally on this basis.

diag_basis := function(N);
    C := CuspForms(N);
    g := Dimension(C);
    w := AtkinLehnerOperator(C,N);
    Vs := [VectorSpace(Rationals(),g)];
    NVs := [];
    for U in Vs do
        BU := Basis(U);
        N1 := Nullspace(w-1) meet U; // split into eigenspaces
        N2 := Nullspace(w+1) meet U;
        NVs := NVs cat [N1,N2];
        Vs := NVs;
    end for;
    new_basis := &cat[Basis(V) : V in NVs | Dimension(V) gt 0];
    T := Matrix(new_basis);
    w := T*w*T^(-1); // diagonalised operator
    B := Basis(C);
    cleardenom := LCM([Denominator(x) : x in Eltseq(T)]);
    NB := [&+[cleardenom*T[i,j]*B[j] : j in [1..g]] : i in [1..g]];
    return NB, w;
end function;

////////////////////////////////////////////

// This function takes as input a level N
// It returns X, E, psi, B, w, cusp. Where:
// X is a nonsingualr projective model for X_0(N) on which w_N acts diagonally
// E is the elliptic curve X_0^+(N) in some Weierstrass form
// psi is the map X -> E
// B is the basis of cusp forms used
// w is the matrix of the AL involution w_N
// cusp is the infinity cusp in X(Q)

model_and_map := function(N);
    B, w := diag_basis(N);
    g := #B;
    X := canonic(B);
    A<[x]> := AmbientSpace(X);
    cusp_seq := []; // find the infinity cusp (as a sequence of coordinates)
    for f in B do
        if Coefficient(f,1) ne 0 then
            cusp_seq := cusp_seq cat [1];
        else cusp_seq := cusp_seq cat [0];
        end if;
    end for;
    cusp := X ! cusp_seq; // the infinity cusp as a point on the curve
    PP := ProjectiveSpace(Rationals(),g-2);
    proj := map<X -> PP | [x[i] : i in [2..g]]>;
    Y := Image(proj); // Quotient curve in P^(g-2)
    AY<[y]> := AmbientSpace(Y);
    assert Genus(Y) eq 1; // verify that the curve has the correct genus
    rho1 := map<X -> Y | [x[i] : i in [2..g]]>;
    assert Degree(rho1) eq 2; // verify that the map has the right degree, so we have the right map and curve
    Z, rho2 := EllipticCurve(Y,rho1(cusp)); // convert into an elliptic curve with Magma
    AZ<[z]> := AmbientSpace(Z);
    E, rho3 := SimplifiedModel(Z); // Weierstrass form of the elliptic curve
    psi := rho1*rho2*rho3;
    assert Conductor(E) eq N;
    return X, E, psi, B, w, cusp;
end function;

////////////////////////////////////////////

// This function checks nonsingularity mod l
// Input: curve X, level N, (infinty) cusp, prime l
// (The infinity cusp can be computed using model_and_map)
// Output True if X is nonsingular mod l, false otherwise

// The function checks X mod l is nonsingular using Lemma 2.3 of the author's paper [1]
// (This is: "Computing quadratic points on modular curves X_0(N)" by Adzaga, Keller, Michaud-Jacobs, Najman, Ozman, and Vukorepa)

is_nonsing_mod_l := function(X, N, cusp, l);
    Xl := ChangeRing(X,GF(l));
    // start with basic checks
    if Dimension(Xl) ge 2 then
        return false;
    end if;
    if IsIrreducible(Xl) eq false then
        return false;
    end if;
    if IsReduced(Xl) eq false then
        return false;
    end if;
    // Now know the curve is integral. We check the genus condition.
    if Genus(Xl) ne Genus(Gamma0(N)) then // Genus(Gamma_0(N)) is the genus of X
        return false;
    end if;
    // We check the curve has a smooth F_l point
    cusp_seq := [GF(l) ! r : r in Eltseq(cusp)];
    cuspl := Xl ! Eltseq(cusp_seq); // Reduction of the cusp mod l
    if IsNonsingular(Xl,cuspl) then // We check if this is a nonsingular point
        return true;
    else return false;
    end if;
end function;
