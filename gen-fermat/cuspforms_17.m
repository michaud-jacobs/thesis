// Magma code to support the computations in the paper On some generalized Fermat equations of the form x^2 + y^2n = z^p by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/gen-fermat for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is at the end of the file

// We start by using the code of Anni and Siksek [1] (very slightly adapted) to eliminate all newforms other than g_1, g_2, g_3, and g_4.

cs:=1; // cs = 1 is i = 1 and cs = 2 is i = 2

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
// returns B_q(ff,\eta,\mu) in the notation of Section 11 of [1].
				
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
// returns B_q(ff) in the notation of Section 11 of [1].
		
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
// returns B_S(ff) in the notation of Section 11 of [1].
		
BS:=function(ff,Off,S);
	B:=&+[Bq(ff,Off,q) : q in S];
	return Integers()!Norm(B);
end function;

// --------------------------------------------------------------------------------------

S:=[3,67,101];  // prime to be used in the sieve

H:=HilbertCuspForms(M,level); 
Hnew:=NewSubspace(H); 
time decomp:=NewformDecomposition(Hnew);
decomp;

if cs eq 1 then 
     interval:=[1..#decomp-4];  // computations cannot be carried out for the last 4 forms (in a reasonable time)
else interval:=[1..#decomp];    // We deal with these separately afterwards
end if;

for i in interval do
	print "+++++++++++";
	print "Dealing with the", i, "-th eigenform";
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

// Output at end of the file

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// We now eliminate the newforms g1,g2,g3, and g4 for all primes l > 5.
// We work directly with the Hecke operators and their characteristic polynomials.

p:=17;
L<zet>:=CyclotomicField(p);
K:=sub<L | zet+1/zet>; 
OK:=Integers(K); 
thj:=OK!(zet+1/zet);      // j = 1
thk:=OK!(zet^4+1/zet^4);  // k = 4

M:=HilbertCuspForms(K,2*OK);
NewM:=NewSubspace(M);

T:=[Factorisation(q*OK)[1][1] : q in [67,3,157]];

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
     print "Doing j = ",j; 
     V := NullSpace(Evaluate(Chpoly1[j][1],M1));
     Vs := Vs cat [* V *];
end for;

time for i in [2..#T] do     

     print "Doing i = ",i; T[i];

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

// Time: 1257.210

Factorisation(Cs[1]);  // 2^17 x 3^8
Factorisation(Cs[2]);  // 2^18 x 3^7 x 5^2
Factorisation(Cs[3]);  // 2^18 x 3^8 x 5^1
Factorisation(Cs[4]);  // 2^20 x 3^2 x 5^2


/* Output

Output for case 1:

+++++++++++
Dealing with the 1 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 26> ]
surviving primes ell= []
+++++++++++
Dealing with the 2 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 28> ]
surviving primes ell= []
+++++++++++
Dealing with the 3 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 24> ]
surviving primes ell= []
+++++++++++
Dealing with the 4 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 34> ]
surviving primes ell= []
+++++++++++
Dealing with the 5 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 24>, <3, 9> ]
surviving primes ell= []
+++++++++++
Dealing with the 6 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 26> ]
surviving primes ell= []
+++++++++++
Dealing with the 7 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 28> ]
surviving primes ell= []
+++++++++++
Dealing with the 8 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 28> ]
surviving primes ell= []
+++++++++++
Dealing with the 9 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) []
surviving primes ell= []
+++++++++++
Dealing with the 10 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) []
surviving primes ell= []
+++++++++++
Dealing with the 11 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 34> ]
surviving primes ell= []
+++++++++++
Dealing with the 12 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) []
surviving primes ell= []
+++++++++++
Dealing with the 13 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 34> ]
surviving primes ell= []
+++++++++++
Dealing with the 14 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 34> ]
surviving primes ell= []
+++++++++++
Dealing with the 15 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 26> ]
surviving primes ell= []
+++++++++++
Dealing with the 16 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 24> ]
surviving primes ell= []
+++++++++++
Dealing with the 17 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 24> ]
surviving primes ell= []
+++++++++++
Dealing with the 18 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 26> ]
surviving primes ell= []
+++++++++++
Dealing with the 19 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 34> ]
surviving primes ell= []
+++++++++++
Dealing with the 20 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) []
surviving primes ell= []
+++++++++++
Dealing with the 21 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 34> ]
surviving primes ell= []
+++++++++++
Dealing with the 22 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 34> ]
surviving primes ell= []
+++++++++++
Dealing with the 23 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 34> ]
surviving primes ell= []
+++++++++++
Dealing with the 24 -th eigenform
this has Hecke eigenvalue field of degree 2
Factoristion of B_S(ff) [ <2, 52> ]
surviving primes ell= []
+++++++++++
Dealing with the 25 -th eigenform
this has Hecke eigenvalue field of degree 2
Factoristion of B_S(ff) [ <2, 52> ]
surviving primes ell= []
+++++++++++
Dealing with the 26 -th eigenform
this has Hecke eigenvalue field of degree 2
Factoristion of B_S(ff) [ <2, 56>, <17, 2> ]
surviving primes ell= []
+++++++++++
Dealing with the 27 -th eigenform
this has Hecke eigenvalue field of degree 2
Factoristion of B_S(ff) [ <2, 52> ]
surviving primes ell= []
+++++++++++
Dealing with the 28 -th eigenform
this has Hecke eigenvalue field of degree 2
Factoristion of B_S(ff) [ <2, 52> ]
surviving primes ell= []
+++++++++++
Dealing with the 29 -th eigenform
this has Hecke eigenvalue field of degree 2
Factoristion of B_S(ff) [ <2, 56> ]
surviving primes ell= []
+++++++++++
Dealing with the 30 -th eigenform
this has Hecke eigenvalue field of degree 6
Factoristion of B_S(ff) [ <2, 80> ]
surviving primes ell= []
+++++++++++
Dealing with the 31 -th eigenform
this has Hecke eigenvalue field of degree 6
Factoristion of B_S(ff) [ <2, 80> ]
surviving primes ell= []

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////

Output for case 2:

+++++++++++
Dealing with the 1 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) []
surviving primes ell= []
+++++++++++
Dealing with the 2 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <3, 5> ]
surviving primes ell= []
+++++++++++
Dealing with the 3 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <3, 5> ]
surviving primes ell= []
+++++++++++
Dealing with the 4 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) []
surviving primes ell= []
+++++++++++
Dealing with the 5 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 10>, <3, 5> ]
surviving primes ell= []
+++++++++++
Dealing with the 6 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 10>, <3, 5> ]
surviving primes ell= []
+++++++++++
Dealing with the 7 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 14> ]
surviving primes ell= []
+++++++++++
Dealing with the 8 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 16>, <3, 7> ]
surviving primes ell= []
+++++++++++
Dealing with the 9 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) []
surviving primes ell= []
+++++++++++
Dealing with the 10 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 14> ]
surviving primes ell= []
+++++++++++
Dealing with the 11 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <3, 5> ]
surviving primes ell= []
+++++++++++
Dealing with the 12 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 14>, <3, 5> ]
surviving primes ell= []
+++++++++++
Dealing with the 13 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 10>, <3, 5> ]
surviving primes ell= []
+++++++++++
Dealing with the 14 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 14> ]
surviving primes ell= []
+++++++++++
Dealing with the 15 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <2, 10>, <3, 5> ]
surviving primes ell= []
+++++++++++
Dealing with the 16 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) []
surviving primes ell= []
+++++++++++
Dealing with the 17 -th eigenform
this has Hecke eigenvalue field of degree 1
Factoristion of B_S(ff) [ <3, 5> ]
surviving primes ell= []
+++++++++++
Dealing with the 18 -th eigenform
this has Hecke eigenvalue field of degree 2
Factoristion of B_S(ff) [ <2, 28>, <5, 4> ]
surviving primes ell= [ 5 ]
+++++++++++
Dealing with the 19 -th eigenform
this has Hecke eigenvalue field of degree 2
Factoristion of B_S(ff) [ <2, 28>, <5, 4> ]
surviving primes ell= [ 5 ]
+++++++++++
Dealing with the 20 -th eigenform
this has Hecke eigenvalue field of degree 4
Factoristion of B_S(ff) [ <2, 40> ]
surviving primes ell= []
+++++++++++
Dealing with the 21 -th eigenform
this has Hecke eigenvalue field of degree 4
Factoristion of B_S(ff) [ <2, 40> ]
surviving primes ell= []
+++++++++++
Dealing with the 22 -th eigenform
this has Hecke eigenvalue field of degree 6
Factoristion of B_S(ff) [ <2, 44>, <5, 8> ]
surviving primes ell= [ 5 ]
+++++++++++
Dealing with the 23 -th eigenform
this has Hecke eigenvalue field of degree 6
Factoristion of B_S(ff) [ <2, 44>, <5, 8> ]
surviving primes ell= [ 5 ]
+++++++++++
Dealing with the 24 -th eigenform
this has Hecke eigenvalue field of degree 8
Factoristion of B_S(ff) [ <2, 40> ]
surviving primes ell= []

*/








