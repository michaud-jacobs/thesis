// Magma code to support the computations in my PhD thesis.

// The code in this file carries out the sieve (incorporating the relative symmetric Chabauty criterion).

// The output is in the file "sieve_output.txt", available at
// https://github.com/michaud-jacobs/thesis/blob/main/cartan/sieve_output.txt

// The code uses data from the file "eqn_data.m" available at:
// https://github.com/michaud-jacobs/thesis/blob/main/cartan/eqn_data.m

load "eqn_data.m";

////////////////////////////////////////////

// The sieve function takes as optional input a different list of auxiliary primes to use
// and an option to set the VerboseLevel to 1
// VerboseLevel 1 includes some additional output

sieve := function(   :primes_for_sieve := [3,5,31,43,53,61,73], VerboseLevel := 0);
    // (non_singularity at the default primes used is checked in the "model.m" file)
    X:= Curve(ProjectiveSpace(R),new_eqns);                 // New model of our curve
    X_plus := Curve(ProjectiveSpace(S), eqn_X_plus);        // The curve X_ns+(13)
    w:= map<X -> X | [Diag[i][i]*R.i : i in [1..8]]>;       // New modular involution
    rho := map< X -> X_plus | new_rho_eqns >;               // New equations for the quotient map
    // We define the seven rational points on the quotient
    SvnPts := [X_plus ! [0,1,0], X_plus ! [0,0,1], X_plus ! [-1,0,1], X_plus ! [1,0,0], X_plus ! [1,1,0], X_plus ! [0,3,2], X_plus ! [1,0,1]];

    ///////////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////////////

    // We form a list of 7 tuples.
    // Each tuple consists of an indexed set of two conjugate quadratic points and their field of definition
    // We use the same code as in the "model.m" file to compute the points

    print "Computing pullbacks of the seven rational points";
    quad_pts_list := [* *];
    for pt in SvnPts do
        pbS := Pullback(rho, pt); // pullback scheme including base scheme
        BS := BaseScheme(rho);
        D := Difference(pbS, BS); // pullback scheme not including base scheme
        pb, K1 := PointsOverSplittingField(D);
        K2 := NumberField(AbsolutePolynomial(K1));
        d := Squarefree(Discriminant(Integers(K2)));
        K<theta> := QuadraticField(d); // simpler form for the quadratic field
        ptsK := Points(D,K);
        quad_pts_list := quad_pts_list cat [*<ptsK, K> *];
        print "Computed pair of known pullback points", ptsK, "where theta^2 =", theta^2;
        print "+++++++";
    end for;
    print "+++++++++++++++++++++++++++++++++++++++++";

    M:=3^10*5^10*13^10*29^10; // Parameter M to be used in the sieve
    A:=AbelianGroup([0,0,0]); // The group Z^3 (the Jacobian has rank 3)

    // initialse data sets

    Ws:=[**];   // list of cosets
    Bs:=[**];   // list of groups
    indices_int := []; // sequence of indices of intersections
    indices_2 := []; // sequence of indices of groups
    coset_sizes_int := []; // sequence of coset sizes of intersections
    coset_sizes_2 := []; // sequence of coset sizes of groups

    B,iA:=sub<A|A>; // initialse B as Z^3
    W:={0*A.1};     // initialise W as the trivial coset

    ///////////////////////////////////////////////////////////////////////////////////////////////

    for p in primes_for_sieve do

        print("Starting calculations for p ="), p;
        H_p:={};    // Build up to list of known points mod p that pass Chabauty test
        Ds_mod_p:=[];    // Build up to list of generators for G reduced mod p
        Rks:=[];      // Ranks of residue disc matrices (used in Chabauty criterion)
        TQ<x> := PolynomialRing(Integers());
        Fp:=GF(p);
        Xp:=ChangeRing(X,Fp);  // Curve mod p

    ///////////////////////////////////////////////////////////////////////////////////////////////

        for i in [1..7] do
            // We start by reducing our quadratic points mod p
            quad_pt := quad_pts_list[i][1];
            K := quad_pts_list[i][2];
            Qa := Eltseq(quad_pt[1]);
            Qb := Eltseq(quad_pt[2]);
            OK:=RingOfIntegers(K);
            dec:=Factorization(p*OK);
            pp:=dec[1][1];                   // A prime above the rational prime p
            f:=InertiaDegree(pp);
            Fpp<t>:= ResidueClassField(pp);  // Either GF(p) or GF(p^2) depending on inertia degree
            Xpp:=ChangeRing(X,Fpp);

            unif:=UniformizingElement(pp);   // Use to reduce point modulo p
            m:=Minimum([Valuation(a,pp) : a in Qa | not a eq 0]);
            Qared:=[unif^(-m)*a : a in Qa];
            Qtaa:=Xpp![Evaluate(a,Place(pp)) : a in Qared]; // Reduction of quadratic point to Xpp
            Qta:=Xp(Fpp) ! Eltseq(Qtaa);
            plQtaa:=Place(Qtaa);
            plQta:=Place(Qta);

            m:=Minimum([Valuation(a,pp) : a in Qb | not a eq 0]); // Repeat with conjugate
            Qbred:=[unif^(-m)*a : a in Qb];
            Qtbb:=Xpp![Evaluate(a,Place(pp)) : a in Qbred];
            Qtb:=Xp(Fpp) ! Eltseq(Qtbb);
            plQtbb:=Place(Qtbb);
            plQtb:=Place(Qtb);

            if Degree(plQta) eq 1 then    // if a point is defined over Fp
                DivQ:=plQta+plQtb;        // then form a divisor from the point and its conjugate
            end if;
            if Degree(plQta) eq 2 then   // if a point is defined over Fp^2
                DivQ:=Divisor(plQta);     // then form the divisor of its place
            end if;

            ////////////////////////////////////////////////////////////////////////////////
            // Checking if there are non-pullback points in residue disc of the point by applying the Chabauty criterion

            wpp:=map< Xpp->Xpp | [x_1,x_2,x_3,-x_4,-x_5,-x_6,-x_7,-x_8] >; // Modular involution
            V,phiD:=SpaceOfDifferentialsFirstKind(Xpp);  // Holomorphic differentials on Xpp
            t:=hom<V->V | [ (Pullback(wpp,phiD(V.i)))@@phiD -V.i  : i in [1..8] ]>;
            T:=Image(t);                                 // The space red(V_0)
            oms:=[phiD(T.i) : i in [1..Dimension(T)]];
            tQta:=UniformizingParameter(Qtaa);
            Ata:=Matrix([[Evaluate(omega/Differential(tQta),plQtaa) : omega in oms]]); // Chabauty criterion matrix
            ra:=Rank(Ata); // Rank 1 means no non-pullback points in residue class, check succeeded
            if ra eq 0 then  // An alert to say that there could potentially be a non-pullback point in the residue class.
                print "Point Not Lonely When i =", i; print"and p =", p;
            end if;

            ////////////////////////////////////////////////////////////////////////////////

            if ra eq 1 then
                H_p :=H_p join {DivQ};    // Include  divisors in the reductions of our known points
            end if;

            if i in [1..3] then          // Reductions of generators for our subgroup G
               Ds_mod_p:=Ds_mod_p cat [DivQ];
            end if;
            if i eq 4 then
               bpp:=DivQ;                // Reduction of our base point
            end if;
        end for;  // End of loop for i = 1 to 7

        if VerboseLevel eq 1 then
            printf "The set H_%o  has %o points", p, #H_p;
            printf "\n";
        end if;

        ///////////////////////////////////////////////

        pls1p:=Places(Xp,1);   // The degree 1 places on Xp
        pls2p:=Places(Xp,2);   //  The degree 2 places on Xp
        degr2:={1*pl1 + 1*pl2 : pl1 in pls1p, pl2 in pls1p} join {1*pl : pl in pls2p};  // Degree 2 divisors on Xp
        if VerboseLevel eq 1 then
            print "There are", #degr2, "degree 2 Update saturation.mdivisors mod", p;
        end if;
        print("Computing the Jacobian mod"),p;
        time C,phi,psi:=ClassGroup(Xp);
        Z:=FreeAbelianGroup(1);
        degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
        JFp:=Kernel(degr);     // This is isomorphic to J_X(F_p)
        print "The Jacobian mod", p, "is isomorphic to", [Order(ee) : ee in Generators(JFp)];
        JFpmodM,pi:=quo<JFp | M*JFp>;
        print "The Jacobian mod M is isomorphic to ", [Order(ee) : ee in Generators(JFpmodM)];

        imGhat:=sub<JFpmodM | [pi(JFp!psi(divp-bpp)) : divp in Ds_mod_p]>; // Image of G in JFpmodM
        S_p:={DD : DD in degr2 |pi((JFp!(psi(DD-bpp)))) in imGhat};  // Set S_{p,M}

        if VerboseLevel eq 1 then
            printf "The set S_%o  has %o points", p, #S_p;
            printf "\n";
        end if;

        T_p:={DD : DD in S_p | not DD in H_p};   // Remove reductions of points in H_{p,M} to obtain T_{p,M}

        if VerboseLevel eq 1 then // We print the points in T_p
            printf "The set T_%o  has %o points. These are:", p, #T_p;
            printf "\n";
            seqT_p := SetToSequence(T_p);
            for divisor in seqT_p do
                place := Decomposition(divisor)[1][1];
                KK<t> := ResidueClassField(place);
                print divisor;
                if Degree(place) gt 1 then
                    print  "where the  miminal polynomial of t is:", MinimalPolynomial(t);
                end if;
            end for;
            if p eq 3 then // We check the exact form of the points presented in the example in the thesis
                print "We write the third point with the same t and check the conjugate points.";
                print "This ensures the written up example matches the computations.";
                places_3 := [*Decomposition(seqT_p[i])[1][1] : i in [1..3] *];
                KK<t> := ResidueClassField(Decomposition(seqT_p[1])[1][1]);
                seq11 := [0,0,0,t^5,t^5,2,t^2,1];
                seq12 := [0,0,0,t^7,t^7,2,t^6,1];
                seq21 := [0,0,0,t^3,t^7,t^7,t^5,1];
                seq22 := [0,0,0,t,t^5,t^5,t^7,1];
                seq31 := [0,0,0,t^3,t^2,t^3,1,0];
                seq32 := [0,0,0,t,t^6,t,1,0];
                assert Place(Xp(KK) ! seq11) eq places_3[1] and Place(Xp(KK) ! seq12) eq places_3[1];
                assert Place(Xp(KK) ! seq21) eq places_3[2] and Place(Xp(KK) ! seq22) eq places_3[2];
                assert Place(Xp(KK) ! seq31) eq places_3[3] and Place(Xp(KK) ! seq32) eq places_3[3];
            end if;
        end if;

        iT_p:=Setseq({pi(JFp!(psi(DD-bpp))) : DD in T_p});  // The set iota_{p,M}(T_{p,M}).

        if VerboseLevel eq 1 then
            printf "The set iota(T_%o)  has %o points", p, #iT_p;
            printf "\n";
            print "These are given by:", iT_p;
            print "(The above numbers will vary with each run)";
        end if;

        phi_p:=hom<A -> JFpmodM | [pi(JFp!psi(divp-bpp)) : divp in Ds_mod_p]>; // The map phi_{p,M}.
        B_p:=Kernel(phi_p);
        B_p,iAp:=sub<A|B_p>;
        ind2 := Index(A,B_p); // index of B_p in Z^3
        indices_2 := indices_2 cat [ind2];
        printf "Index of B_%o in Z^3 is %o", p, ind2;
        printf "\n";
        if VerboseLevel eq 1 then
            print "The group is", B_p;
        end if;
        W_p:={x @@ phi_p : x in iT_p}; // number of cosets
        coset_sizes_2 := coset_sizes_2 cat [#W_p]; 
        printf "W_%o has %o elements", p, #W_p;
        printf "\n";
        if VerboseLevel eq 1 then
            print "These elements are:", W_p;
        end if;
        Ws:=Ws cat [* W_p *];
        Bs:=Bs cat [* B_p *];

        // We now carry out the intersection 
        Bnew,iB_p:=sub<B_p | B meet B_p>;
        iAnew:=iB_p*iAp;
        A0,pi0:=quo<A | iAnew(Bnew)>;
        Ap,pi0p:=quo<A0 | pi0(iAp(B_p))>;
        A1,pi01:=quo<A0 | pi0(iA(B))>;
        pi1:=pi0*pi01;
        pip:=pi0*pi0p;
        W:={x@@pi0 : x in {(pi1(y))@@pi01 +k : y in W, k in Kernel(pi01)} | pi0p(x) in pip(W_p)};
        B:=Bnew;
        iA:=iAnew;
        ind_int := Index(A,B);
        print "Index of B_int in Z^3 is", ind_int;
        if VerboseLevel eq 1 then
            B_print := sub<A | B>;
            print "The group B_int is", B_print;
        end if;
        indices_int := indices_int cat [ind_int];
        coset_sizes_int := coset_sizes_int cat [#W];
        print "W_int has", #W, "elements";
        if VerboseLevel eq 1 then
            print "The set W_int is", W;
        end if;
        print "Calculations completed for p =", p;
        print "+++++++++++++++++++++++++++++++++++++++++";
        if W eq {} then
           print "Sieving complete, success";
           break;
        end if;
    end for;

    if W ne {} then
        print "Sieving complete, unsuccessful";
    end if;

    print "Indices of B_int:", indices_int;
    print "Coset sizes of W_int:", coset_sizes_int;
    return W;
end function;

// See output file "sieve_output.txt";

sieve();
sieve(   :primes_for_sieve := [3,5], VerboseLevel := 1); // For example computations presented in the thesis
