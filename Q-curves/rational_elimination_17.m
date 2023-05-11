// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.27-7.
// The code in this folder ("Q-curves") is based on joint work with Michael A Bennett and Samir Siksek.

// The code in this file carries out the elimination steps for q = 17 and n < 1000 using the rational Frey curve

// The code is taken from the paper
// M. Bennett and S. Siksek, Differences between perfect powers: prime power gaps, arXiv:2110.05553v1 (to appear in Algbera Number Theory)

// In the case n = 7, we use the main function from the file ThueMahlerSolver.m, available at:
// https://github.com/michaud-jacobs/thesis/blob/main/Q-curves/ThueMahlerSolver.m

////////////////////////////////////////////

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

// We now use the refined sieve from to get more information in the case n = 7.

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

// We continue using the code Bennett and Siksek to obtain the Thue--Mahler equations:

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


// load "ThueMahlerSolver.m" // see the file ThueMahlerSolver.m included with this code
// The latest version of this solver can be found at https://github.com/adelagherga/ThueMahler/tree/master/Code/TMSolver

// We obtain the following equations from the 3 partial fails listed above:

// pF 1

// 139*X^7 - 1519*X^6*Y + 7119*X^5*Y^2 - 18515*X^4*Y^3 + 28945*X^3*Y^4 - 27069*X^2*Y^5 + 14133*X*Y^6 - 3137*Y^7
cfs_1 := [ 139, -1519, 7119, -18515, 28945, -27069, 14133, -3137 ];  
sols:=solveThueMahler(cfs_1,[17],1); 
assert sols eq {}; // no solutions

///////////////////////////

// first equation for pF 2

// -17*X^7 + 189*X^6*Y - 861*X^5*Y^2 + 2345*X^4*Y^3 - 3395*X^3*Y^4 + 3591*X^2*Y^5 -1519*X*Y^6 + 467*Y^7
cfs_21 := [ -17, 189, -861, 2345, -3395, 3591, -1519, 467 ];  
sols:=solveThueMahler(cfs_21,[17],1); 
assert sols eq {}; // no solutions

///////////////////////////

// other equation for pF2

cfs_22 := [ -1, 189, -14637, 677705, -16679635, 299923911, -2156762783, 11272244723 ]; 
sols:=solveThueMahler(cfs_22,[17],1); 
assert sols eq { [-1, 0, 0] };  // this leads to the solution (-71)^2 - 17 = 2^7

///////////////////////////

// pF 3 is the same as pF 1, so no solutions.
