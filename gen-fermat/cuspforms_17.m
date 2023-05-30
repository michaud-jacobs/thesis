// Magma code to support the computations in my PhD thesis.

// The code carries out the Hilbert newform elimination steps for signature (2m, 2l, 17)

// The output is in the file "cuspforms_17_output.txt", available at
// https://github.com/michaud-jacobs/thesis/blob/main/gen-fermat/cuspforms_17_output.txt

////////////////////////////////////////////

// We start by using the code of Anni and Siksek (very slightly adapted) to eliminate all newforms other than g_1, g_2, g_3, and g_4.
// This is from the paper:
// S. Anni and S. Siksek. Modular elliptic curves over real abelian fields and the generalized Fermat equation x^2l+y^2m=z^p.
// Algebra Number Theory 10(6):1147--1172, 2016.

for cs in [1,2] do
    print "Doing case", cs;
    p:=17;
    L<zet>:=CyclotomicField(p);
    K:=sub<L | zet+1/zet>; // Q(zeta_p)^+.
    OK:=Integers(K);

    thj:=OK!(zet+1/zet);      // j = 1
    thk:=OK!(zet^4+1/zet^4);  // k = 4

    if  cs eq 1 then            // case 1
        M:=K;
        OO:=Integers(M);
    else                        // case 2
    	M:=Subfields(K,4)[1,1];
    	assert Degree(M) eq 4;  // The unique real subfield of degree 4.
        OO:=Integers(M);
    end if;

    if cs eq 1 then
         P:=Factorisation(p*OO)[1,1];     // Unique prime above 17
         level:=2*OK;
    else
         P:=Factorisation(p*OO)[1,1];     // Unique prime above 17
         level:=2*P;
    end if;

    // --------------------------------------------------------------------------------------

    // Given eta, mu, computes the pair u(eta,mu) and v(eta,mu).

    uv:=function(eta,mu);
    	if cs eq 1 then
    	   u:=(thj+2)*eta^2+(thj-2)*mu^2;
    	   v:=-(thj-2)/(thk-2)*((thk+2)*eta^2+(thk-2)*mu^2);
    	   return u,v;
    	else
    	   u:=((thj+2)*eta^2+(thj-2)*mu^2)/(thj-2);
    	   v:=-((thk+2)*eta^2+(thk-2)*mu^2)/(thk-2);
    	   return u,v;
        end if;
    end function;

    // Given: an eigenform ff; a prime ideal Q of OO; integers eta, mu;
    // returns B_Q(ff,eta,mu)

    BQ:=function(ff,Q,eta,mu);
    	aQ:=HeckeEigenvalue(ff,Q);
    	FQ,piQ:=ResidueClassField(Q);
    	u,v:=uv(eta,mu);
    	w:=-u-v;
    	a2:=piQ(M!(v-u));
    	a4:=piQ(M!(-u*v));
    	if piQ(M!(u^2*v^2*w^2)) eq 0 then
    	   c4:=M!(16*(w^2-u*v));
    	   c6:=M!(-32*(u-v)*(v-w)*(w-u));
    	   gam:=piQ(-c4/c6);
    	   assert gam ne 0;
    	   if IsSquare(gam) then
    		  return ((Norm(Q)+1)-aQ);
    	   else
    		  return ((Norm(Q)+1)+aQ);
    	   end if;
    	 else
    		E:=EllipticCurve([0,a2,0,a4,0]);
    		return (TraceOfFrobenius(E)-aQ);
    	 end if;
    end function;

    // Given: an eigenform ff; the maximal order Off of the field of Hecke eigenvalues Off;
    // a rational prime q; integers eta, mu;
    // returns B_q(ff,\eta,\mu) in the notation of Section 11 of Anni and Siksek's paper.

    Bqetamu:=function(ff,Off,q,eta,mu);
    		 Qlist:=[fact[1] : fact in Factorisation(q*OO)];
    		 B:=0*Off;
    		 for Q in Qlist do
    			 B:=B+BQ(ff,Q,eta,mu)*Off;
    		 end for;
    		 return B;
    end function;

    // Given:
    // an eigenform ff; the maximal order Off of the field of Hecke eigenvalues Off;
    // a rational prime q;
    // returns B_q(ff) in the notation of Section 11 of of Anni and Siksek's paper.

    Bq:=function(ff,Off,q);
    	B:=q*Off;
    	for eta, mu in [0..(q-1)] do
    		if (eta ne 0 or mu ne 0) then
    		   B:=B*(Bqetamu(ff,Off,q,eta,mu));
    		end if;
    	end for;
    	return B;
    end function;

    // Given: an eigenform ff; the maximal order Off of the field of Hecke eigenvalues Off;
    // a set S of rational primes q different from 2, p
    // returns B_S(ff) in the notation of Section 11 of Anni and Siksek's paper.

    BS:=function(ff,Off,S);
    	B:=&+[Bq(ff,Off,q) : q in S];
    	return Integers()!Norm(B);
    end function;

    // --------------------------------------------------------------------------------------

    S:=[3,67,101];  // primes to be used in the sieve

    H:=HilbertCuspForms(M,level);
    Hnew:=NewSubspace(H);
    print "Computing newform decomposition";
    time decomp:=NewformDecomposition(Hnew); // full newform decomposition
    decomp;

    if cs eq 1 then
        interval:=[1..#decomp-4];  // computations cannot be carried out for the last 4 forms of case 1 (in a reasonable time), we consider these afterwards
    else
        interval:=[1..#decomp];   
    end if;
    print "Starting newform elimination";
    for i in interval do
    	print "+++++++++++";
    	print "Dealing with the", i, "-th newform";
    	V:=decomp[i];
    	ff:=Eigenform(V);
    	Qff:=HeckeEigenvalueField(V);
    	print "this has Hecke eigenvalue field of degree", Degree(Qff);
    	Off:=MaximalOrder(Qff);
    	B:=BS(ff,Off,S);
    	print "Factoristion of B_S(ff)", Factorisation(B);
    	survivors:=[l : l in PrimeDivisors(Norm(B)) | l in {2,3,p} eq false];
    	print "surviving primes ell=", survivors;
    end for;

    //////////////////////////////////////////
    //////////////////////////////////////////
    if cs eq 1 then
        print "+++++++++++++++++++++++++++++++";
        print "Considering final four newforms";
        // We now eliminate the newforms g1,g2,g3, and g4 for all primes l > 5.
        // These are the four remaining forms for case 1
        // We work directly with the Hecke operators and their characteristic polynomials.
        // We use the same basic code as in Chapter 7 
        // (see the "hecke_elim" function in the "newform_elimination_functions.m" file in the "flt" folder)

        p:=17;
        L<zet>:=CyclotomicField(p);
        K:=sub<L | zet+1/zet>;
        OK:=Integers(K);
        thj:=OK!(zet+1/zet);      // j = 1
        thk:=OK!(zet^4+1/zet^4);  // k = 4

        M:=HilbertCuspForms(K,2*OK);
        NewM:=NewSubspace(M);

        T:=[Factorisation(q*OK)[1][1] : q in [67,3,157]]; // primes to use in sieve, ordered like this to reduce computation time
        // We now define the functions we need to obtain the appropriate quanitites by working with the characteristic polynomial factors, rather than the eigenvalues themselves

        uv:=function(eta,mu);
            u:=(thj+2)*eta^2+(thj-2)*mu^2;
            v:=-(thj-2)/(thk-2)*((thk+2)*eta^2+(thk-2)*mu^2);
            return u,v;
        end function;

        BfQetamu:=function(Q,e,eta,mu);
                 FQ,piQ:=ResidueClassField(Q);
        	     u,v:=uv(eta,mu);
        	     w:=-u-v;
        	     a2:=piQ(K!(v-u));
        	     a4:=piQ(K!(-u*v));
                 if piQ(K!(u^2*v^2*w^2)) eq 0 then
        	        c4:=K!(16*(w^2-u*v));
        	        c6:=K!(-32*(u-v)*(v-w)*(w-u));
        	        gam:=piQ(-c4/c6);
        	        assert gam ne 0;
        	        if IsSquare(gam) then
        		       return Integers() ! (Norm(Q)*Evaluate(e,Norm(Q)+1));
        	        else
        		       return Integers() ! (Norm(Q)*Evaluate(e,-Norm(Q)-1));
        	        end if;
        	     else
        		    E:=EllipticCurve([0,a2,0,a4,0]);
        		    return Integers() ! (Norm(Q)*Evaluate(e,TraceOfFrobenius(E)));
        	     end if;
        end function;

        Bf:=function(Q,e);
             q:=PrimeFactors(Integers()! (Norm(Q)))[1];
             Bs:=[];
             for eta, mu in [0..(q-1)] do
        		if eta ne 0 or mu ne 0 then
        		   Bs:= Bs cat [(BfQetamu(Q,e,eta,mu))];
        		end if;
        	end for;
            B:=LCM(Bs);
        	return B;
        end function;
        
        // We now start the subspace decomposition process

        time H1:=HeckeOperator(NewM,T[1]);
        M1:=Matrix(H1);
        time Chpoly1:=Factorisation(CharacteristicPolynomial(M1));

        Cs:=[*Bf(T[1],e[1]) : e in Chpoly1*];
        Newind:=[(#Cs-3)..#Cs];   // isolates the forms g1, g2, g3, and g4
        Cs:=[*Cs[i] : i in Newind*];
        Es:=[* [Chpoly1[i][1]] : i in Newind*];
        Vs:=[* *];

        // Start by computing the list of irreducible subspaces corresponding to the first Hecke operator
        time for j in Newind do
            V := NullSpace(Evaluate(Chpoly1[j][1],M1));
            Vs := Vs cat [* V *];
        end for;

        time for i in [2..#T] do
            H:=HeckeOperator(NewM,T[i]);
            M:=Matrix(H);
            NVs:=[* *];
            NCs:=[* *];
            NEs:=[* *];
            for j in [1..#Vs] do
                B:=Basis(Vs[j]);
                Coords:=[Coordinates(Vs[j],H(B[k])) : k in [1..#B] ];
                NM:=Matrix(Coords);
                Chpoly:=Factorisation(CharacteristicPolynomial(NM));
                NVsj:=[* *];
                NCsj:=[* *];
                NEsj:=[* *];
                for e in Chpoly do
                    basns:= Basis(  NullSpace( Evaluate(e[1],NM) )  );
                    subsp:= sub< Vs[j] | [ &+[basns[l][k]*B[k] : k in [1..#B] ]  :  l in [1..#basns] ]>;
                    NVsj:=NVsj cat [* subsp *];
                    NC:= GCD(Cs[j],Bf(T[i],e[1])); // gcd of previous norm and new norm
                    NCsj:=NCsj cat [* NC *];
                    Ne:=Es[j] cat [e[1]];
                    NEsj:=NEsj cat [* Ne *];
                end for;
                NVs:=NVs cat NVsj;
                NCs:=NCs cat NCsj;
                NEs:=NEs cat NEsj;
            end for;
            Vs:=NVs;
            Cs:=NCs;
            Es:=NEs;
        end for;

        print "Factorisations of the newform values are:";
        Factorisation(Cs[1]);  // Output: 2^17 x 3^8
        Factorisation(Cs[2]);  // Output: 2^18 x 3^7 x 5^2
        Factorisation(Cs[3]);  // Output: 2^18 x 3^8 x 5^1
        Factorisation(Cs[4]);  // Output: 2^20 x 3^2 x 5^2
    end if;
    print "+++++++++++++++++++++++++++++++++++++";
end for;
