canonic := function(B);
    N := Level(B[1]);
    prec := 5*N;
    dim:=#B;
    L<q>:=LaurentSeriesRing(Rationals(),prec);
    R<[x]>:=PolynomialRing(Rationals(),dim);
    Bexp:=[L!qExpansion(B[i],prec) : i in [1..dim]];
    eqns:=[R | ];
	d:=1;
	tf:=false;
	while tf eq false do
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

    indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];
	indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)

    eqns := [LCM([Denominator(c) : c in Coefficients(eqn)])*eqn : eqn in eqns]; // scale equations
    X := Curve(ProjectiveSpace(R),eqns); // same curve with scaled equations

	for eqn in eqns do
		wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound for Gamma_0(N)
	    Bexp1:=[qExpansion(B[i],hecke+10) : i in [1..dim]]; // q-expansions
		assert Valuation(Evaluate(eqn,Bexp1)) gt hecke+1;
	end for; // We have now checked the correctness of the equations for X.

 return(X);
end function;

diag_basis := function(N);
    C := CuspForms(N);
    g := Dimension(C);
    w := AtkinLehnerOperator(C,N);
    Vs := [VectorSpace(Rationals(),g)];
    NVs := [];
    for U in Vs do
        BU := Basis(U);
        N1 := Nullspace(w-1) meet U;
        N2 := Nullspace(w+1) meet U;
        NVs := NVs cat [N1,N2];
        Vs := NVs;
    end for;
    new_basis := &cat[Basis(V) : V in NVs | Dimension(V) gt 0];
    T := Matrix(new_basis);
    w := T*w*T^(-1);
    B := Basis(C);
    cleardenom := LCM([Denominator(x) : x in Eltseq(T)]);
    NB := [&+[cleardenom*T[i,j]*B[j] : j in [1..g]] : i in [1..g]];
    return NB, w;
end function;

model_and_map := function(N);
    B, w := diag_basis(N);
    g := #B;
    X := canonic(B);
    A<[x]> := AmbientSpace(X);
    cusp_seq := [];
    for f in B do
        if Coefficient(f,1) ne 0 then
            cusp_seq := cusp_seq cat [1];
        else cusp_seq := cusp_seq cat [0];
        end if;
    end for;
    cusp := X ! cusp_seq;
    PP := ProjectiveSpace(Rationals(),g-2);
    proj := map<X -> PP | [x[i] : i in [2..g]]>;
    Y := Image(proj);
    AY<[y]> := AmbientSpace(Y);
    assert Genus(Y) eq 1;
    rho1 := map<X -> Y | [x[i] : i in [2..g]]>;
    assert Degree(rho1) eq 2;
    Z, rho2 := EllipticCurve(Y,rho1(cusp));
    AZ<[z]> := AmbientSpace(Z);
    E, rho3 := SimplifiedModel(Z);
    psi := rho1*rho2*rho3;
    assert Conductor(E) eq N;
    return X, E, psi, B, w;
end function;
