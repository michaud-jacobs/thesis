// This Magma code carries out the checks and computations for the paper 
// Q-curves and the Lebesgue-Nagell equation

q := 41; // Choose q = 17, 41, 89, or 97.
M<rootq> := QuadraticField(q);
OM :=Integers(M);

// start by defining gamma and gammab appropriately and check they satisfy requirements.

if q eq 17 then                    
   gamma := (-3+rootq)/2;
   gammab := (-3-rootq)/2;
   assert gamma*gammab eq -2;
   _,red := quo<OM | gamma^2>;
   assert IsZero(red(rootq+1));
   assert IsZero(red(gammab+1));
   fac1 := Factorisation(2*OM)[1][1];
   fac2 := Factorisation(2*OM)[2][1];
   assert gamma*OM eq fac1;
   assert gammab*OM eq fac2;
end if;

if q eq 41 then 
   //delta := 32 + 5*rootq;
   //deltab:= 32 - 5*rootq;
   gamma := (-19 - 3*rootq)/2;
   gammab := (-19 + 3*rootq)/2;
   assert gamma*gammab eq -2;
   _,red := quo<OM | gamma^2>;
   assert IsZero(red(rootq+1));
   assert IsZero(red(gammab+1));
   fac1 := Factorisation(2*OM)[1][1];
   fac2 := Factorisation(2*OM)[2][1];
   assert gamma*OM eq fac1;
   assert gammab*OM eq fac2;
end if;

if q eq 89 then
   //delta := 500 + 53*rootq;
   //deltab := 500 - 53*rootq;
   gamma := (9+rootq)/2;
   gammab := (9-rootq)/2;
   assert gamma*gammab eq -2;
   _,red := quo<OM | gamma^2>;
   assert IsZero(red(rootq+1));
   assert IsZero(red(gammab+1));
   fac1 := Factorisation(2*OM)[1][1];
   fac2 := Factorisation(2*OM)[2][1];
   assert gamma*OM eq fac1;
   assert gammab*OM eq fac2;
end if;

if q eq 97 then 
   delta := 5604 + 569*rootq;
   deltab := 5604 - 569*rootq;
   gamma := (325+33*rootq)/2;
   gammab := (325-33*rootq)/2;
   assert gamma*gammab eq -2;
   _,red := quo<OM | gamma^2>;
   assert IsZero(red(rootq+1));
   assert IsZero(red(gammab+1));
   fac1 := Factorisation(2*OM)[1][1];
   fac2 := Factorisation(2*OM)[2][1];
   assert gamma*OM eq fac1;
   assert gammab*OM eq fac2;
end if;

////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////  

// k = 2m is even is cs 1
// k = 2m+1 is odd is cs 2

// Input: x between 0 and p-1, m between 0 and p-2, a prime p, a case number cs.
// Output: Trace of Frobenius at a prime of M above p for the given values of x and m.

QTracexmp := function(x,m,p,cs);
         pp := Factorisation(p*OM)[1][1]; // A prime of M above p
         npp := Norm(pp);
         Fpp<t>, redpp := ResidueClassField(pp); // redpp reduces mod pp 
         rootq_pp := redpp(rootq);
         gamma_pp := redpp(gamma);
         gammab_pp := redpp(gamma);
         if cs eq 1 then 
            w_pp := ((x + q^(2*m)*rootq_pp)*(rootq_pp)^3)/2;
            wb_pp := ((x - q^(2*m)*rootq_pp)*(-rootq_pp)^3)/2;
         end if;
         if cs eq 2 then 
            w_pp := ((x + q^(2*m+1)*rootq_pp)*(rootq_pp))/2;
            wb_pp := ((x - q^(2*m+1)*rootq_pp)*(-rootq_pp))/2;
         end if;
         // assert w_pp + wb_pp eq redpp(q^(2*m+2)); // sanity check
         Disc_pp := (gamma_pp^12)*(gammab_pp^6)*(w_pp)^2*(wb_pp);
         if IsZero(Disc_pp) eq false then 
            E_pp := EllipticCurve([0,2*gamma_pp*(redpp(q)^(m+1)),0,(gamma_pp^2)*w_pp,0]);
            app := TraceOfFrobenius(E_pp);
            return app;
         end if;
         if IsZero(Disc_pp) eq true then
            c4_pp := (gamma_pp^6)*(gammab_pp^4)*(w_pp + 4*wb_pp);
            c6_pp := (gamma_pp^9)*(gammab_pp^6)*(w_pp - 8*wb_pp)*(redpp(q))^(m+1);
            g := -c6_pp/c4_pp;   // we use this to determine split or non-split multiplicative reduction
            if IsSquare(g) then 
               app := npp + 1;
            else app := -npp -1;
            end if;
            return app;
         end if;
end function;

// We compute a set of all possible traces at a prime above p (both cases at once).

Traces_atp := function(p);
    Traces:= {};
    for x,m in [0..p-1] do  // here we take m = p-1 too, this isn't necessary, can just go up to m-2
        Traces := Traces join {QTracexmp(x,m,p,1),QTracexmp(x,m,p,2)};  // we do both cases here
    end for;
    return Traces;
end function; 

////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////  

// We construct the newforms with the appropriate level and character

eps:=DirichletGroup(2*q^2).1;  // This is our quadratic Dirichlet character
assert Conductor(eps) eq q;      
assert Order(eps) eq 2;
MM := ModularForms(eps,2);   // Space of modular forms of weight 2, level 2*q^2, and character eps
S :=CuspidalSubspace(MM);
N := NewSubspace(S);
dim := Dimension(N);
time Nfs := Newforms(S);
class_sizes := [#cl : cl in Nfs];  
Nfreps:= [*Nfs[i][1] : i in [1..#Nfs]*];  // Choose a newform representative for each Galois conjugacy class.

////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////  

// We now try and eliminate newforms

// function to compute the trace of Frob at a newform

TrFrobpd:=function(g,p);  // Use g for newforms here (but f is used in the paper).
          if IsInert(p,OM) then 
             Tr := Coefficient(g,p)^2- 2*eps(p)*p;  // could just say +2p as eps(p) = -1 when p is inert.
          else Tr := Coefficient(g,p);
          end if;
          return Tr;
end function;

// Input a newform g and a prime p
// Output Bgp value
Bgp := function(g,p);
    Trgp := TrFrobpd(g,p);
    return Integers() ! (p*(Norm(&*[TrEp - Trgp : TrEp in Traces_atp(p)])));
end function;

// Input a newform g
// Output Bg value, obtained using primes above the rational primes between 3 and 30, with p ne q.

Bg := function(g);
   return GCD([Bgp(g,p) : p in PrimesInInterval(3,30) | p ne q ]);
end function;

// see output file for the output of the following loop.

for i in [1..#Nfreps] do   // Do not use for q = 97 and the last two newforms as too slow.
    print "Doing i = ", i;
    time BB := Bg(Nfreps[i]);
    if BB ne 0 then 
       PrimeFactors(BB);
    else BB;
    end if;
    print " +++++++++++++++++++";
end for;

////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////  

// For q = 97 and the last two newforms we can use the following.
// The last two newforms are Nfreps[28] and Nfreps[29].

g := Nfreps[28];  // 28 or 29
p := 3; // p = 3 splits in M = Q(root(97)), so simplifies calculations
c3 := Coefficient(g,p);
time m3 := MinimalPolynomial(c3); // just under 10 minutes

Pfacs3 := {};
for TrEp in Traces_atp(p) do
    Pfacs3 := Pfacs3 join Set(PrimeFactors(Integers() ! (Evaluate(m3,TrEp))));
end for;

// for 28 this is { 97, 197, 19699, 221213147, 103253033370303849827500533626642567989 }
// for 29 this is { 7, 97, 293, 26459, 29009, 21800662421, 1646462350472829319981822308933239 }

p := 11; // splits in M
c11 := Coefficient(g,p);
time m11 := MinimalPolynomial(c11); // just under 10 minutes

Pfacs11 := {};
for TrEp in Traces_atp(p) do
    Pfacs11 := Pfacs11 join Set(PrimeFactors(Integers() ! (Evaluate(m11,TrEp))));
end for;

// for 28 this is { 97, 197, 883, 51178639, 61636609, 228584903, 260653637, 424065307, 2917870913, 338663262251, 1018649743327, 1240078052149, 35721870807713, 182813673735166315687, 26463327294255127678711, 1078920696877023743158459, 6128931136469659192656731, 1267552850875731186890958647077, 619359364442343315454986086059486285753242163 }
// for 29 this is { 7, 97, 197, 293, 881, 2549, 21757, 160033, 203878319, 4102431803, 23093935003, 145485956351, 55026131560360852193, 513177834834375493931, 3273015333063381240971, 6909497652223021076438783, 447830839329396958965849731, 986120937021833473419484284121336988471, 18057580031646431274412356196478878566887588673345137195371 }

Pfacs3 meet Pfacs11; 

// for 28 this is { 97, 197 } 
// for 29 this is { 7, 97, 293 }  

////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////     

// Now we use the multi-Frey approach for q = 41

q := 41;
p := 7;
pp := Factorisation(p*OM)[1][1];
g := Newforms(CuspForms(2*q))[1][1];
assert Coefficient(g,p) eq -4;

// The following function computes the trace at a prime p of G_{x,m} for a given x and m
// (This is more detailed than necessary for the case q = 41).

// cs 1 is k = 2m is even
// cs 2 is k = 2m+1 is odd 
RatTracexmp := function(x, m, p, cs);
        Fp := GF(p);       
        x := Fp ! x;
        if cs eq 1 then
           k := 2*m;
        end if;
        if cs eq 2 then 
           k := 2*m+1;
        end if; 
        Weier := [0,4*x,0,4*(x^2-q^(2*k+1)),0];
        if IsEllipticCurve(Weier) then 
           ap := TraceOfFrobenius(EllipticCurve(Weier));
           return ap;
        else a_1 := 0; a_2 := 4*x; a_3 := 0; a_4 := 4*(x^2-q^(2*k+1)); a_6 := 0;
             b_2 := a_1^2 + 4*a_2; b_4 := a_1*a_3 + 2*a_4; b_6 := a_3^2 + 4*a_6;
             c4 := b_2^2 - 24*b_4;
             c6 := -b_2^3 + 36*b_2*b_4 - 216*b_6;
             g := Fp ! (-c6/c4); 
             if IsSquare(g) then 
                ap := p + 1;
             else ap := -p -1;
             end if;
             return ap;
        end if;
end function;


for x,m in [0..p-1] do
   <RatTracexmp(x,m,p,1),x,m>;   // only x = 6 mod 7 gives a trace of -4.
   <RatTracexmp(x,m,p,2),x,m>;   // Independent of cs
end for;

// We have 
for m in [0..p-2] do
    assert QTracexmp(6,1,p,1) eq 6; // when x is 6 mod 7, both traces are 6
    assert QTracexmp(6,1,p,2) eq 6; 
end for;

// However, for the two newforms we were unable to eliminate we have:

assert TrFrobpd(Nfreps[1],p) eq -4;
assert TrFrobpd(Nfreps[4],p) eq 14;

////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////     

// We check for q = 17 or q = 89 that when we enter the true solution (-23)^2 - 17 = 2^9 or (-91)^2 - 89 = 2^13
// that the traces of the Frey Q-curve match those of the obstructing form

q := 89;  // 17 or 89
if q eq 17 then 
   f := Nfreps[3]; // the obstructing newform
   x := -23;
elif q eq 89 then 
   f := Nfreps[1]; // the obstructing newform
   x := -91;
end if;

w := ((x+rootq)/2)*(rootq^3);
EE:=EllipticCurve([0,2*gamma*q,0,(gamma^2)*w,0]);
assert Conductor(EE) eq gamma*gammab*rootq^2*OM;  // right conductor
LocalInformation(EE,rootq*OM); 
j := jInvariant(EE);
assert Valuation(j, rootq*OM) gt -1; // it is = 0.

for p in [p : p in PrimesInInterval(3,1000) | p ne q] do
    pp := Factorisation(p*OM)[1][1];
    assert TraceOfFrobenius(EE,pp) eq TrFrobpd(f,p);
end for;



////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////     

// We now use the code from the paper 
// [4] M. Bennett and S. Siksek, Differences between perfect powers: prime power gaps, arXiv:2110.05553v1
// to verify there are no unkown solutions for q = 17 and n > 7

kraus:=function(v,q,del,kap,f,nn);
	// This computes the intersection \cap \mathcal{Z}_{\ell_i}
	// where \ell_i are the primes l = tn+1
	// with l \ne q
	// and t at most 200.
	// The class of k mod (2n) belongs to this intersection.
	if Type(nn) eq RngIntElt then
		n:=nn;
	else
		n:=PrimeDivisors(Norm(nn))[1];
	end if;
	assert IsPrime(n);
	assert v in [0,1];
	assert del in [0,1];
	assert kap in [1,5];
	//assert 2^kap*q eq Level(f);
	mlist:=[ m : m in [0..(2*n-1)] | m mod 2 eq v and IsDivisibleBy(2*m+1,n) eq false ];
	t:=0;
	lset:=[];
	repeat
		t:=t+2;
		l:=t*n+1;
		if IsPrime(l) and l ne q then	
			if Type(f) eq CrvEll then
				cl:=TraceOfFrobenius(f,l);
			else
				cl:=Coefficient(f,l);
			end if;
			Fl:=GF(l);
			gl:=PrimitiveElement(Fl);
			gln:=gl^n;
			ql:=Fl!q;
			if Valuation(4-cl^2,nn) eq 0 or IsSquare((-1)^(del+1)*ql) eq false then
				Append(~lset,l);
				ynset:=[gln^s : s in [0..(t-1)]];
				mlistNew:=[];
				for m in mlist do
					qlm:=(-1)^(del+1)*ql^(2*m+1);
					flag:=false;
					cnt:=0;
					while cnt lt #ynset and flag eq false do
						cnt:=cnt+1;
						yn:=ynset[cnt];
						zsq:=yn+qlm;
						tf,z1:=IsSquare(zsq);
						//yn:=(z^2+(-1)^del*ql^(2*m+1));
						if tf then
							for z in [z1,-z1] do
							if kap eq 1 then
								G:=[0,4*z,0,4*yn,0];	
							else
								if IsDivisibleBy(q-(-1)^del,4) then
									G:=[0,-4*z,0,4*yn,0];	
								else
									G:=[0,2*z,0,yn,0];	
								end if;
							end if;
							G:=EllipticCurve(G);
							if cl in Integers() and n^2 gt 4*l then
								Q:=Random(G);
								if (l+1-Integers()!cl)*Q eq G!0 then
									if Trace(G) eq cl then
										flag:=true;
										//Include(~mlistNew,m);
									end if;
								end if;
							else
								a:=Trace(G);
								if Valuation(a-cl,nn) ge 1 then
									flag:=true;
									//Include(~mlistNew,m);
								end if;
							end if;
							end for;
						end if;
					end while;
					if flag then
						Append(~mlistNew,m);
					end if;
				end for;
				mlist:=mlistNew;
			end if;
		end if;
	until #mlist eq 0 or t gt 200;				
	return mlist, lset;
end function;

// We now test all exponenets between 7 and 1000

for n in PrimesInInterval(7,1000) do
    for v in [0,1] do
        Int :=  kraus(v,17,1,1,EllipticCurve([1,0,0,-3,1]), n);
        if #Int gt 0 then 
           <n,v>, Int;
        end if;
    end for;
end for;

// Output: <7,0> [2], <7,1> [1,5,9]
// So only need to do consider prime exponent 7.

////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////

// We use the refined sieve from [4] to get more information in the case n = 7.

fineKraus:=function(mlist,q,del,kap,f,nn);
	if Type(nn) eq RngIntElt then
		n:=nn;
	else
		n:=PrimeDivisors(Norm(nn))[1];
	end if;
	assert IsPrime(n);
	assert del in [0,1];
	assert kap in [1,5];
	if del eq 0 then
		M<th>:=QuadraticField(-q);
	else
		M<th>:=QuadraticField(q);
	end if;
	OM:=MaximalOrder(M);
	C,phi:=ClassGroup(OM);
	assert IsCyclic(C);
	P:=Factorisation(2*OM)[1,1];
	assert sub<C | P@@phi> eq C;  // The prime ideal above 2 generates the class group.
	if kap eq 1 and #C eq n then
		return [* *]; // There is a class group obstruction in this case
				// Namely ((x+q^k th)/2) OO_M = B^(n-2) A^n 
				// where A is an ideal, and B is either P or its conjugate.
				// Now A^n is principal, but B^(n-2) is not principal
				// giving a contradiction.
	end if;
	if kap eq 1 then
		S:=[];
		for i in [0..(#C)-1] do
			tf,bet:=IsPrincipal(P^(n*(1-i)-2));		
			if tf then
				bet:=M!bet;
				S:=S cat [2*bet, 2*Conjugate(bet)];
			end if;
		end for;
	else
		S:=[];
		for i in [0..#(C)-1] do
			tf,bet:=IsPrincipal(P^(-i*n));		
			if tf then
				bet:=M!bet;
				S:=S cat [bet];
			end if;
		end for;
	end if;
	if del eq 1 then
		eps:=OM!FundamentalUnit(M);
		b:=(n-1) div 2;
		S:=[eta*eps^r : r in [-b..b], eta in S];
	end if;
	pairs:=[* [* m, eta *] : m in mlist, eta in S *];
	t:=0;
	repeat
		t:=t+2;
		l:=t*n+1;
		if IsPrime(l) and l ne q and KroneckerSymbol((-1)^(del+1)*q,l) eq 1 then	
			cl:=Coefficient(f,l);
			Fl:=GF(l);
			ql:=Fl!q;
			if Valuation(4-cl^2,nn) eq 0  then
				tf,sql:=IsSquare((-1)^(del+1)*ql);
				assert tf;
				sql:=Integers()!sql;
				L:=l*OM+(th-sql)*OM;
				assert Norm(L) eq l;
				assert IsPrime(L);
				FL,piL:=ResidueClassField(L);
				pairsNew:=[* *];
				for pr in pairs do
					m:=pr[1];
					eta:=pr[2];
					assert 2^(n*#C)*eta in OM;
					pieta:=piL(OM!(2^(n*#C)*eta))/piL(OM!(2^(n*#C)));
					for z in Fl do
						yn:=(z^2+(-1)^del*ql^(2*m+1));
						if yn^t eq 1 then
							if kap eq 1 then
								G:=[0,4*z,0,4*yn,0];	
							else
								if IsDivisibleBy(q-(-1)^del,4) then
									G:=[0,-4*z,0,4*yn,0];	
								else
									G:=[0,2*z,0,yn,0];	
								end if;
							end if;
							G:=EllipticCurve(G);
							a:=Trace(G);
							if Valuation(a-cl,nn) ge 1 then
								if (piL(Integers()!z+q^m*th)/pieta)^t eq 1 then
									pairsNew:=pairsNew cat [* [* m, eta *]*];	
									break;
								end if;	
							end if;
						end if;
					end for;
				end for;
				pairs:=pairsNew;
			end if;
		end if;
	until #pairs eq 0 or t gt 800;				
	return [[pr[1]] cat Eltseq(M!pr[2]) : pr in pairs];
end function;

// We apply the refined sieve
f := Newforms(CuspForms(34))[1][1];

fineKraus([2],17,1,1,f,7); // output [ [ 2, -573, 139 ] ]
fineKraus([1,5,9],17,1,1,f,7); // output [ [ 1, 71, -17 ], [ 9, 573, -139 ]]

// we have the following partialFails

// Each partial fail is [q,del,kap,v,n, triple from the ouput of fineKraus]

partialFails := [ [17, 1, 1, 0, 7, 2, -573, 139],
                  [17, 1, 1, 1, 7, 1,  71,  -17],
                  [17, 1, 1, 1, 7, 9, -573, 139] ];

// We use the code of [4] to obtain the Thue--Mahler equations:

for pF in partialFails do
    print "Partial Fail is ",pF;
	q,del,kap,v,n,m,et1,et2:=Explode(pF);
	q:=Integers()!q;
	del:=Integers()!del;
	n:=Integers()!n;
	M<t>:=QuadraticField((-1)^(del+1)*q);
	OM:=Integers(M);
	eta:=(et1+et2*t);
	if kap eq 1 then
		assert OM.2 eq (1+t)/2;
		eta:=OM!(eta/2);
		bet1,bet2:=Explode(Eltseq(eta));
		assert eta eq bet1+bet2*OM.2;
		QXY<X,Y>:=PolynomialRing(Rationals(),2);
		QXYT<T>:=PolynomialRing(QXY);
        	QXYth<th>:=quo<QXYT | Evaluate(MinimalPolynomial(OM.2),T)>;
		f,g:=Explode(Eltseq((bet1+bet2*th)*(X+Y*th)^n));
	else
		bet1,bet2:=Explode(Eltseq(M!eta));
		assert eta eq bet1+bet2*t;
		QXY<X,Y>:=PolynomialRing(Rationals(),2);
		QXYT<T>:=PolynomialRing(QXY);
        	QXYth<th>:=quo<QXYT | Evaluate(MinimalPolynomial(t),T)>;
		f,g:=Explode(Eltseq((bet1+bet2*th)*(X+Y*th)^n));
	end if;
	g1,A,bb:=MinRedBinaryForm(g);
	if bb eq 1 and Determinant(A) in [1,-1] then
		Ainv:=A^-1;
	else
		g1:=g;
		Ainv:=Matrix([[1,0],[0,1]]);
	end if;
	if g ne Evaluate(g1,[Ainv[1,1]*X+Ainv[1,2]*Y,Ainv[2,1]*X+Ainv[2,2]*Y]) then
		g1:=-g1;
	end if;
	assert g eq Evaluate(g1,[Ainv[1,1]*X+Ainv[1,2]*Y,Ainv[2,1]*X+Ainv[2,2]*Y]);
	C:=MonomialCoefficient(g1,X^n);
    for a in Divisors(AbsoluteValue(Integers()!C)) do
		gC:=Evaluate(g1,Y,a*Y);
		D:=GCD([Integers()!c: c in Coefficients(gC)]);
		gCD:=gC/D;
		if Set(PrimeDivisors(D)) subset {q} then
			QU<U>:=PolynomialRing(Rationals());
               		h:=Evaluate(gCD,[1,U]);
			assert Degree(h) eq n;
			assert #Factorisation(h) eq 1;
               		cfs:=Coefficients(h);
               		cfs:=[Integers()!(c) : c in cfs];
                    print "Coefficients are ",cfs;

        end if;
     end for;
end for;


// pF 1

139*X^7 - 1519*X^6*Y + 7119*X^5*Y^2 - 18515*X^4*Y^3 + 28945*X^3*Y^4 - 27069*X^2*Y^5 + 14133*X*Y^6 - 3137*Y^7;
cfs := [ 139, -1519, 7119, -18515, 28945, -27069, 14133, -3137 ];  // no solutions


// first equation for pF 2

-17*X^7 + 189*X^6*Y - 861*X^5*Y^2 + 2345*X^4*Y^3 - 3395*X^3*Y^4 + 3591*X^2*Y^5 -1519*X*Y^6 + 467*Y^7
cfs := [ -17, 189, -861, 2345, -3395, 3591, -1519, 467 ];   // no solutions

// other equation for pF2

cfs := [ -1, 189, -14637, 677705, -16679635, 299923911, -2156762783, 11272244723 ];  // sols := {[ -1, 0, 0 ]}
// this leads to the solution (-71)^2 - 17 = 2^7


// pF 3, same as pF 1

139*X^7 - 1519*X^6*Y + 7119*X^5*Y^2 - 18515*X^4*Y^3 + 28945*X^3*Y^4 - 27069*X^2*Y^5 + 14133*X*Y^6 - 3137*Y^7
cfs := [ 139, -1519, 7119, -18515, 28945, -27069, 14133, -3137 ];  // no solutions


load "ThueMahlerSolver.m" // see the file ThueMahlerSolver.m included with the code

// Now test each sequence of coefficients.
sols:=solveThueMahler(cfs,1,[17]); // This works on Magma V2.25-3, but may not work on certain later versions.

