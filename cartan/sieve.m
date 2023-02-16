// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.26-10

// The code in this file carries out the sieving (and Chabauty) steps.

// The output is in the file sieve_output.txt, available at
// https://github.com/michaud-jacobs/thesis/blob/main/cartan/sieve_output.txt

// The code uses data from the file "eqn_data.m" file available at:
// https://github.com/michaud-jacobs/thesis/blob/main/cartan/eqn_data.m

load "eqn_data.m";

X:= Curve(ProjectiveSpace(R),new_eqns);                 // New model of our curve
X_plus := Curve(ProjectiveSpace(S), eqn_X_plus);        //  The curve X_ns^+(13)
w:= map<X -> X | [Diag[i][i]*R.i : i in [1..8]]>;       // New modular involution
rho := map< X -> X_plus | new_rho_eqns >;               // New equations for map

SvnPts := [X_plus ! [0,1,0], X_plus ! [0,0,1], X_plus ! [-1,0,1], X_plus ! [1,0,0], X_plus ! [1,1,0], X_plus ! [0,3,2], X_plus ! [1,0,1]]; 

///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////

// We form a list of 7 tuples.
// Each tuple consists of an indexed set of two conjugate quadratic points and their field of definition

quad_pts_list := [* *];
for pt in SvnPts do
    S := Pullback(rho, pt);
    BS := BaseScheme(rho);
    D := Difference(S, BS);
    pb, K1 := PointsOverSplittingField(D);
    K2 := NumberField(AbsolutePolynomial(K1));
    d := Squarefree(Discriminant(Integers(K2)));
    K := QuadraticField(d);
    ptsK := Points(D,K);  
    quad_pts_list := quad_pts_list cat [*<ptsK, K> *];
end for;

primes_for_sieve:=[3,5,31,43,53,61,73];  // Primes to be used in sieve 
// Nonsingularity at these primes was verified in the model.m file

M:=3^10*5^10*13^10*29^10; // Parameter M to be used in the sieve
A:=AbelianGroup([0,0,0]); // The group Z^3 (the Jacobian has rank 3)

Ws:=[**]; 
Bs:=[**];
indices_int := [];
indices_2 := [];
coset_sizes_int := [];
coset_sizes_2 := [];

B,iA:=sub<A|A>; 
W:={0*A.1};     

///////////////////////////////////////////////////////////////////////////////////////////////

for p in primes_for_sieve do 

    print("Starting calculations for p ="), p;
    H_p:={};    // Build up to list of known points mod p that pass Chabauty test
    Ds_mod_p:=[];    // Build up to list of generators for G reduced mod p
    Rks:=[];      // Ranks of residue disc matrices
    TQ<x> := PolynomialRing(Integers()); 
    Fp:=GF(p);
    Xp:=ChangeRing(X,Fp); 

///////////////////////////////////////////////////////////////////////////////////////////////

    for i in [1..7] do     
        quad_pt := quad_pts_list[i][1];
        K := quad_pts_list[i][2];                  
        Qa := Eltseq(quad_pt[1]);
        Qb := Eltseq(quad_pt[2]);         
        // Code now continues in same way as Sieve_OldMagma.m
                                
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

       if Degree(plQta) eq 1 then   // if a point is defined over Fp
           DivQ:=plQta+plQtb;        // then form a divisor from the point and its conjugate
        end if;
        if Degree(plQta) eq 2 then   // if a point is defined over Fp^2
           DivQ:=Divisor(plQta);     // then form the divisor of its place
        end if;

        ////////////////////////////////////////////////////////////////////////////////
        // Checking if there are exceptional points in residue disc of the point

        wpp:=map< Xpp->Xpp | [x_1,x_2,x_3,-x_4,-x_5,-x_6,-x_7,-x_8] >; // Modular involution
        V,phiD:=SpaceOfDifferentialsFirstKind(Xpp);  // Holomorphic differentials on Xpp
        t:=hom<V->V | [ (Pullback(wpp,phiD(V.i)))@@phiD -V.i  : i in [1..8] ]>; 
        T:=Image(t);                                 // The space red(V_0)
        oms:=[phiD(T.i) : i in [1..Dimension(T)]]; 
        tQta:=UniformizingParameter(Qtaa);  
        Ata:=Matrix([[Evaluate(omega/Differential(tQta),plQtaa) : omega in oms]]);
        ra:=Rank(Ata); // Rank 1 means no exceptional points in residue class
        if ra eq 0 then  // An alert to say that there could potentially be an exceptional point in the residue class.
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

///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////

    pls1p:=Places(Xp,1);   // The degree 1 places on Xp 
    pls2p:=Places(Xp,2);   //  The degree 2 places on Xp 
    degr2:={1*pl1 + 1*pl2 : pl1 in pls1p, pl2 in pls1p} join {1*pl : pl in pls2p};  //Degree 2 divisors on Xp
    print("Computing the Jacobian mod"),p;
    time C,phi,psi:=ClassGroup(Xp); 
    Z:=FreeAbelianGroup(1);
    degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;  
    JFp:=Kernel(degr);     // This is isomorphic to J_X(\F_p)
    print "The Jacobian mod", p, "is isomorphic to", [Order(ee) : ee in Generators(JFp)];
    JFpmodM,pi:=quo<JFp | M*JFp>; 
    print "The Jacobian mod M is isomorphic to ", [Order(ee) : ee in Generators(JFpmodM)];
    
    imGhat:=sub<JFpmodM | [pi(JFp!psi(divp-bpp)) : divp in Ds_mod_p]>; // Image of G in JFpmodM
    S_p:={DD : DD in degr2 |pi((JFp!(psi(DD-bpp)))) in imGhat};  // Set S_{p,M}
    T_p:={DD : DD in S_p | not DD in H_p};   // Remove reductions of points in H_{p,M} to obtain T_{p,M}
    iT_p:=Setseq({pi(JFp!(psi(DD-bpp))) : DD in T_p});  // The set iota_{p,M}(T_{p,M}).

    phi_p:=hom<A -> JFpmodM | [pi(JFp!psi(divp-bpp)) : divp in Ds_mod_p]>; // The map phi_{p,M}.
    B_p:=Kernel(phi_p);  
    B_p,iAp:=sub<A|B_p>; 
    ind2 := Index(A,B_p);
    indices_2 := indices_2 cat [ind2];
    printf "Index of B_%o in Z^3 is %o", p, ind2; 
    printf "\n";
    W_p:={x @@ phi_p : x in iT_p}; 
    coset_sizes_2 := coset_sizes_2 cat [#W_p];
    printf "W_%o has %o elements", p, #W_p;
    printf "\n";
    Ws:=Ws cat [* W_p *];  
    Bs:=Bs cat [* B_p *];

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
    indices_int := indices_int cat [ind_int];
    coset_sizes_int := coset_sizes_int cat [#W];
    print "W_int has", #W, "elements";
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
