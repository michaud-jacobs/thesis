// Note : Could also just look at which abelian varieties are in the + or - eigenspaces of the AL-involutions, as this should give the coefficients right away (this is effevtively what we are doing anyway...), maybe you could find a general argument to prove the result for many p or 2p, you would need the existence of a rank 0 factor in certain minus eigenspaces I think, just like the Eisenstein quotient is a factor of the minus eigenspace of X_0(p).

N:=122;
S:=CuspForms(N);
R<q>:=PowerSeriesRing(Integers());

J:=JZero(N);
dec:=Decomposition(J); // the decomposition of J_0(74)

/* Output:
[
    Modular abelian variety 122A of dimension 1, level 2*61 and conductor 2*61
    over Q,
    Modular abelian variety 122B of dimension 2, level 2*61 and conductor
    2^2*61^2 over Q,
    Modular abelian variety 122C of dimension 3, level 2*61 and conductor
    2^3*61^3 over Q,
    Modular abelian variety N(61,122,1)(61A) of dimension 1, level 2*61 and
    conductor 61 over Q,
    Modular abelian variety N(61,122,2)(61A) of dimension 1, level 2*61 and
    conductor 61 over Q,
    Modular abelian variety N(61,122,1)(61B) of dimension 3, level 2*61 and
    conductor 61^3 over Q,
    Modular abelian variety N(61,122,2)(61B) of dimension 3, level 2*61 and
    conductor 61^3 over Q
]
*/

for d in dec do
    Dimension(d),  IsZeroAt(LSeries(d),1);
end for;

// False means the abelian variety has rank 0.

/*
1 true
2 false
3 false
1 true
1 true
3 false
3 false
*/

f1:=Newforms("122A")[1];
f2:=Newforms("122B")[1];
f3:=Newforms("122C")[1];

f1 := Newform(dec[1]);
f2 := Newform(dec[2]);
f3 := Newform(dec[3]);


Nfs:=[*f1,f2,f3*];

ALs:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1]; // Atkin--Lehner indices

// By applying the AL involutions we compute the expansions at other cusps for each newform

CuspExps:=[Nfs]; // Initial list

for m in ALs do
    CE:=[* *];
    for f in Nfs do

        K:= CoefficientField(f);
        RK:= ChangeRing(R,K);
        SK:= BaseChange(S,K);
        fexp := qExpansion(f,50); // Increase precision to uniquely determine form
        fK:= SK ! (RK ! fexp);
        fKm:=AtkinLehnerOperator(m,fK);
        CE:= CE cat [*fKm*];
     end for;
     CuspExps:=CuspExps cat [CE];
end for;

// We compute the 4 formal immersion matrices, F_inf, F_inf,2, F_inf,3, and F_inf,4
// Output included after the loop

Cusp1:=1; // 1 <--> infinity,
for i in [1,2,3,4] do
    Cusp2 := i; // i <--> ALs[i](infinity) for i = 2,3,4.

    Col1:=[Integers() ! Coefficient(f,1) : f in CuspExps[Cusp1]]; // First column of matrix

    if Cusp1 eq Cusp2 then
        Col2 := [Integers() ! Coefficient(f,2) : f in CuspExps[Cusp1]]; // Second column of matrix
    else Col2 := [Integers() ! Coefficient(f,1) : f in CuspExps[Cusp2]]; // Second column of matrix
    end if;
    c1 := Transpose(Matrix([Col1]));
    c2 := Transpose(Matrix([Col2]));
    F_inf_i := HorizontalJoin(c1,c2);
    print  F_inf_i;
    print "++++++++++++++++++++";
end for;

// We see that at each matrix has rank 2 modulo q for any prime q > 2.
/* Output:

[ 1 -1]
[ 1 -1]
[ 1  1]
++++++++++++++++++++
[ 1  1]
[ 1  1]
[ 1 -1]
++++++++++++++++++++
[ 1  1]
[ 1 -1]
[ 1  1]
++++++++++++++++++++
[ 1  1]
[ 1 -1]
[ 1 -1]
++++++++++++++++++++

*/
