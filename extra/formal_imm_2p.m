for p in PrimesInInterval(29,100) do
print "p = ", p;
N := 2*p;
S:=CuspForms(N);
R<q>:=PowerSeriesRing(Integers());
J:=JZero(N);
dec := Decomposition(J);
Nfs := [* *];
for d in dec do
    if IsZeroAt(LSeries(d),1) eq false then
        Nfs := Nfs cat [*Newform(d)*];
    end if;
end for;

ALs:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];


CuspExps:=[Nfs]; // Initial list

for m in ALs do
    CE:=[* *];
    for f in Nfs do
        K:= CoefficientField(f);
        RK:= ChangeRing(R,K);
        SK:= BaseChange(S,K);
        prec := Max(100,Ceiling(N /3));
        fexp := qExpansion(f,prec); // Increase precision to uniquely determine form
        fK:= SK ! (RK ! fexp);
        fKm:=AtkinLehnerOperator(m,fK);
        CE:= CE cat [*fKm*];
     end for;
     CuspExps:=CuspExps cat [CE];
end for;

for i in [2,3,4] do
    Cusp2 := i; // i <--> ALs[i](infinity) for i = 2,3,4.
    Col2 := [Integers() ! Coefficient(f,1) : f in CuspExps[Cusp2]]; // Second column of matrix
    Col1 := [1 : i in [1..#Col2]];
    M := Transpose(Matrix(Integers(), [Col1,Col2]));
    //Col2min := [Col2[i] - Col2[1] : i in [1..#Col2]];
    //assert IsZero(Col2min) eq false;
    M;
    assert IsSubsequence(PrimeFactors(GCD(Minors(M,2))),[2]);
    print("++++++");
end for;
print("+++++++++++++++++++++");

// Up to p = 100 we can check inf + inf using the trace form for all primes q
// if we wish to completely avoid working over larger fields
/*
M := Matrix(Integers(), [[Trace(Coefficient(f,1)),Trace(Coefficient(f,2))] : f in Nfs]);
// <N, GCD(Minors(M,2))>;
assert GCD(Minors(M,2)) ne 0;
assert IsSubsequence(PrimeFactors(GCD(Minors(M,2))),[2]);
*/

// Let's see what happens if we use the Trace form for all forms:
// Mainly works fine, a few issues at 3 and 5 for some p < 100.

for i in [2,3,4] do
Cusp2 := i; // i <--> ALs[i](infinity) for i = 2,3,4.
Col2 := [Integers() ! Trace(Coefficient(f,1)) : f in CuspExps[Cusp2]]; // Second column of matrix
Col1 := [Integers() ! Trace(Coefficient(f,1)) : f in CuspExps[1]];
M := Transpose(Matrix(Integers(), [Col1,Col2]));
M;
PrimeFactors(GCD(Minors(M,2)));
print("++++++");
end for;
print("+++++++++++++++++++++");
end for;

/*
p := 37;
N := 2*p;
S:=CuspForms(N);
R<q>:=PowerSeriesRing(Integers());
J:=JZero(N);
dec := Decomposition(J);
Nfs := [* *];
for d in dec do
    if IsZeroAt(LSeries(d),1) eq false then
        Nfs := Nfs cat [*Newform(d)*];
    end if;
end for;

ALs:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];


bigfs := [* f : f in Nfs | Degree(f) gt 1*]; // REPETITION PROBLEM HERE
smallfs := [* f : f in Nfs | Degree(f) eq 1*];

Tups := [];
for q in PrimesInInterval(2,2000) do
    fail := 0;
    coeffs_q := [*Coefficient(f,q) : f in bigfs*];
    for c in coeffs_q do
        deg_c := Degree(MinimalPolynomial(c));
        if deg_c gt 1 then
            fail := 1;
            break;
        end if;
    end for;
    if fail eq 1 then
        continue;
    end if;
    Tq := HeckeOperator(S,q);
    for i in [1..#coeffs_q] do
        c := coeffs_q[i];
        f := bigfs[i];
        dim_c := Dimension(Eigenspace(Tq,c));
        if dim_c ne Degree(f) then
            fail := 1;
            break;
        end if;
    end for;
    if fail eq 1 then
        continue;
    end if;
    if fail eq 0 then
        Tups := Tups cat [<q> cat <c : c in coeffs_q>];
        //break;
    end if;
end for;

B := Basis(S);

i := 1;
q := Tups[i][1];
Tq:=HeckeOperator(S,q);
coeffs_q := [*Tups[i][j] : j in [2..#Tups[i]]*];
Es := [*Basis(Eigenspace(Tq,c))[1] : c in coeffs_q *];

NB := [   &+[e[i]*B[i] : i in [1..#B]] : e in Es] cat [S ! (R !f) : f in smallfs];
*/




// Try using integral bases by working with conjugates
for p in PrimesInInterval(29,300) do
print "p = ", p;
N := 2*p;
S:=CuspForms(N);
R<q>:=PowerSeriesRing(Integers());
J:=JZero(N);
dec := Decomposition(J);
Nfs := [* *];
for d in dec do
    if IsZeroAt(LSeries(d),1) eq false then
        Nfs := Nfs cat [*Newform(d)*];
    end if;
end for;
basis := [ ];
for f in Nfs do
    K:= CoefficientField(f);
    RK:= ChangeRing(R,K);
    SK:= BaseChange(S,K);
    prec := Max(100,Ceiling(N /3));
    fexp := qExpansion(f,prec); // Increase precision to uniquely determine form
    fK:= SK ! (RK ! fexp);
    OK := Integers(K);
    bOK := Basis(OK);
    for b in bOK do
        bfK := b*fK;
        tr_bfK := S ! (R ! (&+[Trace(Coefficient(bfK,i))*q^i : i in [1..prec-1]] + O(q^(prec-1))));
        basis := basis cat [tr_bfK];
    end for;
end for;

CuspExps:=[*basis*]; // Initial list
ALs:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
for m in ALs do
    CE:=[* *];
    for f in basis do
        fm:=AtkinLehnerOperator(m,f);
        CE:= CE cat [*fm*];
     end for;
     CuspExps:=CuspExps cat [*CE*];
end for;

for i in [2,3,4] do
    Cusp2 := i; // i <--> ALs[i](infinity) for i = 2,3,4.
    Col2 := [Integers() ! Coefficient(f,1) : f in CuspExps[Cusp2]]; // Second column of matrix
    Col1 := [1 : i in [1..#Col2]];
    M := Transpose(Matrix(Integers(), [Col1,Col2]));
    //M;
    assert IsSubsequence(PrimeFactors(GCD(Minors(M,2))),[2]);
    print("++++++");
end for;
print("+++++++++++++++++++++");
end for;



























N := 65;
f1 := Newforms("65B")[1];
K1<a1> := CoefficientField(f1);
A1, phi1, psi1 := AutomorphismGroup(K1);
tau1 := psi1(A1.1);

f3 := Newforms("65C")[1];
K3<a3> := CoefficientField(f3);
A3, phi3, psi3 := AutomorphismGroup(K3);
tau3 := psi3(A3.1);

K<b> := Compositum(K1,K3);

f1_coeffs_1 := [K ! (Coefficient(f1,i)) : i in [1..3]];
f1_coeffs_5 := f1_coeffs_1;
f1_coeffs_13 := [-a : a in f1_coeffs_1];
f1_coeffs_65 := f1_coeffs_13;

f2_coeffs_1 := [K ! (tau1(Coefficient(f1,i))) : i in [1..3]];
f2_coeffs_5 := f2_coeffs_1;
f2_coeffs_13 := [-a : a in f2_coeffs_1];
f2_coeffs_65 := f2_coeffs_13;

f3_coeffs_1 := [K ! (Coefficient(f3,i)) : i in [1..3]];
f3_coeffs_5 := [-a : a in f3_coeffs_1];
f3_coeffs_13 := f3_coeffs_1;
f3_coeffs_65 := f3_coeffs_5;

f4_coeffs_1 := [K ! (tau3(Coefficient(f3,i))) : i in [1..3]];
f4_coeffs_5 := [-a : a in f4_coeffs_1];
f4_coeffs_13 := f4_coeffs_1;
f4_coeffs_65 := f4_coeffs_5;

OK := Integers(K);
p := 3*OK;
k, q := quo<OK | p>;

p2 := 2*OK;
k2, q2 := quo<OK | p2>;

// inf + inf + inf

M1 := Matrix([f1_coeffs_1,f2_coeffs_1,f3_coeffs_1]);
q(Determinant(M1)); // NOT ZERO
assert q2(Determinant(M1)) eq 0;

M2 := Matrix([f2_coeffs_1,f3_coeffs_1,f4_coeffs_1]);
q(Determinant(M2)); // NOT ZERO
assert q2(Determinant(M2)) eq 0;

// inf + inf + c5

M3 := Matrix([  [f1_coeffs_1[1], f1_coeffs_1[2], f1_coeffs_5[1]],
                [f2_coeffs_1[1], f2_coeffs_1[2], f2_coeffs_5[1]],
                [f3_coeffs_1[1], f3_coeffs_1[2], f3_coeffs_5[1]]
                ]);
q(Determinant(M3)); // NOT ZERO
assert q2(Determinant(M3)) eq 0;

// inf + inf + c13

M4 := Matrix([  [f1_coeffs_1[1], f1_coeffs_1[2], f1_coeffs_13[1]],
                [f2_coeffs_1[1], f2_coeffs_1[2], f2_coeffs_13[1]],
                [f3_coeffs_1[1], f3_coeffs_1[2], f3_coeffs_13[1]]
                ]);
q(Determinant(M4)); // NOT ZERO
assert q2(Determinant(M4)) eq 0;

// inf + inf + c65

M5 := Matrix([  [f1_coeffs_1[1], f1_coeffs_1[2], f1_coeffs_65[1]],
                [f2_coeffs_1[1], f2_coeffs_1[2], f2_coeffs_65[1]],
                [f3_coeffs_1[1], f3_coeffs_1[2], f3_coeffs_65[1]]
                ]);
q(Determinant(M5)); // IS ZERO
Determinant(M5); // ALSO ZERO

// Can try by using fourth cusp form too

M6 := Matrix([  [f1_coeffs_1[1], f1_coeffs_1[2], f1_coeffs_65[1]],
                [f2_coeffs_1[1], f2_coeffs_1[2], f2_coeffs_65[1]],
                [f3_coeffs_1[1], f3_coeffs_1[2], f3_coeffs_65[1]],
                [f4_coeffs_1[1], f4_coeffs_1[2], f4_coeffs_65[1]]
                ]);
Rank(M6); // Rank is 2 over K, so will not be a formal immersion mod any prime.
// The 65 one seems to casue problems as this links with the comment about X_0+(65)



// c5 + c5 + c65

M7 := Matrix([  [f1_coeffs_5[1], f1_coeffs_5[2], f1_coeffs_65[1]],
                [f2_coeffs_5[1], f2_coeffs_5[2], f2_coeffs_65[1]],
                [f3_coeffs_5[1], f3_coeffs_5[2], f3_coeffs_65[1]]
                ]);
q(Determinant(M7)); // NOT ZERO
assert q2(Determinant(M7)) eq 0;

// c5 + c5 + c13

M8 := Matrix([  [f1_coeffs_5[1], f1_coeffs_5[2], f1_coeffs_13[1]],
                [f2_coeffs_5[1], f2_coeffs_5[2], f2_coeffs_13[1]],
                [f3_coeffs_5[1], f3_coeffs_5[2], f3_coeffs_13[1]],
                [f4_coeffs_5[1], f4_coeffs_5[2], f4_coeffs_13[1]]
                ]);
Rank(M8); // Rank 2

// c5 + c5 + c1

M9 := Matrix([  [f1_coeffs_5[1], f1_coeffs_5[2], f1_coeffs_1[1]],
                [f2_coeffs_5[1], f2_coeffs_5[2], f2_coeffs_1[1]],
                [f3_coeffs_5[1], f3_coeffs_5[2], f3_coeffs_1[1]]
                ]);
q(Determinant(M9)); // NOT ZERO
assert q2(Determinant(M9)) eq 0;

// c1 + c5 + c13

M10 := Matrix([  [f1_coeffs_1[1], f1_coeffs_5[1], f1_coeffs_13[1]],
                [f2_coeffs_1[1], f2_coeffs_5[1], f2_coeffs_13[1]],
                [f3_coeffs_1[1], f3_coeffs_5[1], f3_coeffs_13[1]],
                [f4_coeffs_1[1], f4_coeffs_5[1], f4_coeffs_13[1]]
                ]);
Rank(M10); // Rank 2

// c1 + c5 + c65

M11 := Matrix([  [f1_coeffs_1[1], f1_coeffs_5[1], f1_coeffs_65[1]],
                [f2_coeffs_1[1], f2_coeffs_5[1], f2_coeffs_65[1]],
                [f3_coeffs_1[1], f3_coeffs_5[1], f3_coeffs_65[1]],
                [f4_coeffs_1[1], f4_coeffs_5[1], f4_coeffs_65[1]]
                ]);
Rank(M11); // Rank 2

// c5 + c13 + c65

M12 := Matrix([  [f1_coeffs_5[1], f1_coeffs_13[1], f1_coeffs_65[1]],
                [f2_coeffs_5[1], f2_coeffs_13[1], f2_coeffs_65[1]],
                [f3_coeffs_5[1], f3_coeffs_13[1], f3_coeffs_65[1]],
                [f4_coeffs_5[1], f4_coeffs_13[1], f4_coeffs_65[1]]
                ]);
Rank(M12); // Rank 2

// c1 + c13 + c65

M13 := Matrix([  [f1_coeffs_1[1], f1_coeffs_13[1], f1_coeffs_65[1]],
                [f2_coeffs_1[1], f2_coeffs_13[1], f2_coeffs_65[1]],
                [f3_coeffs_1[1], f3_coeffs_13[1], f3_coeffs_65[1]],
                [f4_coeffs_1[1], f4_coeffs_13[1], f4_coeffs_65[1]]
                ]);
Rank(M13); // Rank 2

// c5 + c5 + c5

M14 := Matrix([f1_coeffs_5,f2_coeffs_5,f3_coeffs_5]);
q(Determinant(M14)); // NOT ZERO
assert q2(Determinant(M14)) eq 0;

// c13 + c13 + c13

M15 := Matrix([f1_coeffs_13,f2_coeffs_13,f3_coeffs_13]);
q(Determinant(M15)); // NOT ZERO
assert q2(Determinant(M15)) eq 0;

// c65 + c65 + c65

M16 := Matrix([f1_coeffs_65,f2_coeffs_65,f3_coeffs_65]);
q(Determinant(M16)); // NOT ZERO
assert q2(Determinant(M16)) eq 0;



// So all the three separate cusps give det 0
// and some of the 2 + 1 cusp give det 0
// None of the 3 cusps give det 0

// Working mod 2, we always get determinant 0

// We now check that results are the same as when using the other basis.

M := CuspForms(N);
B := Basis(M);
R<q> := PowerSeriesRing(Integers());
A := HeckeOperator(M,199);
Eigenvalues(A); // { <20, 2>, <-16, 1>, <4, 2> }
E1 := Basis(Eigenspace(A,-16));
E2 := Basis(Eigenspace(A,20));
E3 := Basis(Eigenspace(A,4));

betterBasis :=
  [
      &+[E1[1][i]*B[i] : i in [1..#B]],
      &+[E2[1][i]*B[i] : i in [1..#B]],
      &+[E2[2][i]*B[i] : i in [1..#B]],
      &+[E3[1][i]*B[i] : i in [1..#B]],
      &+[E3[2][i]*B[i] : i in [1..#B]]
  ];

 f1 := betterBasis[2];
 f2 := betterBasis[3];
 f3 := betterBasis[4];
 f4 := betterBasis[5];

 f1_coeffs_1 := [Coefficient(f1,i) : i in [1..3]];
 f1_coeffs_5 := [Coefficient(AtkinLehnerOperator(5,f1),i) : i in [1..3]];
 f1_coeffs_13 := [Coefficient(AtkinLehnerOperator(13,f1),i) : i in [1..3]];
 f1_coeffs_65 := [Coefficient(AtkinLehnerOperator(65,f1),i) : i in [1..3]];

 f2_coeffs_1 := [Coefficient(f2,i) : i in [1..3]];
 f2_coeffs_5 := [Coefficient(AtkinLehnerOperator(5,f2),i) : i in [1..3]];
 f2_coeffs_13 := [Coefficient(AtkinLehnerOperator(13,f2),i) : i in [1..3]];
 f2_coeffs_65 := [Coefficient(AtkinLehnerOperator(65,f2),i) : i in [1..3]];

 f3_coeffs_1 := [Coefficient(f3,i) : i in [1..3]];
 f3_coeffs_5 := [Coefficient(AtkinLehnerOperator(5,f3),i) : i in [1..3]];
 f3_coeffs_13 := [Coefficient(AtkinLehnerOperator(13,f3),i) : i in [1..3]];
 f3_coeffs_65 := [Coefficient(AtkinLehnerOperator(65,f3),i) : i in [1..3]];

 f4_coeffs_1 := [Coefficient(f4,i) : i in [1..3]];
 f4_coeffs_5 := [Coefficient(AtkinLehnerOperator(5,f4),i) : i in [1..3]];
 f4_coeffs_13 := [Coefficient(AtkinLehnerOperator(13,f4),i) : i in [1..3]];
 f4_coeffs_65 := [Coefficient(AtkinLehnerOperator(65,f4),i) : i in [1..3]];

// We should now be able to form the same matrices as before and get the same results
// for the formal immersion critera.
// The 3x3 matrices may not have the same ranks, but the 4x3 should



// inf + inf + inf

M1 := Matrix([f1_coeffs_1,f2_coeffs_1,f3_coeffs_1]);
(Determinant(M1)) mod 3; // ZERO, DIFFERENT FROM BEFORE... BUT

M2 := Matrix([f2_coeffs_1,f3_coeffs_1,f4_coeffs_1]);
(Determinant(M2)) mod 3; // NOT ZERO


// inf + inf + c5

M3 := Matrix([  [f1_coeffs_1[1], f1_coeffs_1[2], f1_coeffs_5[1]],
                [f2_coeffs_1[1], f2_coeffs_1[2], f2_coeffs_5[1]],
                [f3_coeffs_1[1], f3_coeffs_1[2], f3_coeffs_5[1]]
                ]);
(Determinant(M3); // -2, so not zero mod 3

// inf + inf + c13

M4 := Matrix([  [f1_coeffs_1[1], f1_coeffs_1[2], f1_coeffs_13[1]],
                [f2_coeffs_1[1], f2_coeffs_1[2], f2_coeffs_13[1]],
                [f3_coeffs_1[1], f3_coeffs_1[2], f3_coeffs_13[1]]
                ]);
Determinant(M4); // 2, so not zero mod 3

// inf + inf + c65

M5 := Matrix([  [f1_coeffs_1[1], f1_coeffs_1[2], f1_coeffs_65[1]],
                [f2_coeffs_1[1], f2_coeffs_1[2], f2_coeffs_65[1]],
                [f3_coeffs_1[1], f3_coeffs_1[2], f3_coeffs_65[1]]
                ]);
Determinant(M5)// ZERO
// Can try by using fourth cusp form too

M6 := Matrix([  [f1_coeffs_1[1], f1_coeffs_1[2], f1_coeffs_65[1]],
                [f2_coeffs_1[1], f2_coeffs_1[2], f2_coeffs_65[1]],
                [f3_coeffs_1[1], f3_coeffs_1[2], f3_coeffs_65[1]],
                [f4_coeffs_1[1], f4_coeffs_1[2], f4_coeffs_65[1]]
                ]);
Rank(M6); // Rank is 2, so will not be a formal immersion mod any prime.
// Same as before

// c5 + c5 + c65

M7 := Matrix([  [f1_coeffs_5[1], f1_coeffs_5[2], f1_coeffs_65[1]],
                [f2_coeffs_5[1], f2_coeffs_5[2], f2_coeffs_65[1]],
                [f3_coeffs_5[1], f3_coeffs_5[2], f3_coeffs_65[1]]
                ]);
Determinant(M7); // -2

// c5 + c5 + c13

M8 := Matrix([  [f1_coeffs_5[1], f1_coeffs_5[2], f1_coeffs_13[1]],
                [f2_coeffs_5[1], f2_coeffs_5[2], f2_coeffs_13[1]],
                [f3_coeffs_5[1], f3_coeffs_5[2], f3_coeffs_13[1]],
                [f4_coeffs_5[1], f4_coeffs_5[2], f4_coeffs_13[1]]
                ]);
Rank(M8); // Rank 2

// c5 + c5 + c1

M9 := Matrix([  [f1_coeffs_5[1], f1_coeffs_5[2], f1_coeffs_1[1]],
                [f2_coeffs_5[1], f2_coeffs_5[2], f2_coeffs_1[1]],
                [f3_coeffs_5[1], f3_coeffs_5[2], f3_coeffs_1[1]]
                ]);
Determinant(M9); // 2

// c1 + c5 + c13

M10 := Matrix([  [f1_coeffs_1[1], f1_coeffs_5[1], f1_coeffs_13[1]],
                [f2_coeffs_1[1], f2_coeffs_5[1], f2_coeffs_13[1]],
                [f3_coeffs_1[1], f3_coeffs_5[1], f3_coeffs_13[1]],
                [f4_coeffs_1[1], f4_coeffs_5[1], f4_coeffs_13[1]]
                ]);
Rank(M10); // Rank 2

// c1 + c5 + c65

M11 := Matrix([  [f1_coeffs_1[1], f1_coeffs_5[1], f1_coeffs_65[1]],
                [f2_coeffs_1[1], f2_coeffs_5[1], f2_coeffs_65[1]],
                [f3_coeffs_1[1], f3_coeffs_5[1], f3_coeffs_65[1]],
                [f4_coeffs_1[1], f4_coeffs_5[1], f4_coeffs_65[1]]
                ]);
Rank(M11); // Rank 2

// c5 + c13 + c65

M12 := Matrix([  [f1_coeffs_5[1], f1_coeffs_13[1], f1_coeffs_65[1]],
                [f2_coeffs_5[1], f2_coeffs_13[1], f2_coeffs_65[1]],
                [f3_coeffs_5[1], f3_coeffs_13[1], f3_coeffs_65[1]],
                [f4_coeffs_5[1], f4_coeffs_13[1], f4_coeffs_65[1]]
                ]);
Rank(M12); // Rank 2

// c1 + c13 + c65

M13 := Matrix([  [f1_coeffs_1[1], f1_coeffs_13[1], f1_coeffs_65[1]],
                [f2_coeffs_1[1], f2_coeffs_13[1], f2_coeffs_65[1]],
                [f3_coeffs_1[1], f3_coeffs_13[1], f3_coeffs_65[1]],
                [f4_coeffs_1[1], f4_coeffs_13[1], f4_coeffs_65[1]]
                ]);
Rank(M13); // Rank 2

// c5 + c5 + c5

M14 := Matrix([f1_coeffs_5,f2_coeffs_5,f3_coeffs_5]);
Determinant(M14); // ZERO, BUT:

M14b := Matrix([f1_coeffs_5,f2_coeffs_5,f4_coeffs_5]);
Determinant(M14b); // -2


// c13 + c13 + c13

M15 := Matrix([f1_coeffs_13,f2_coeffs_13,f3_coeffs_13]);
Determinant(M15); // ZERO, BUT:

M15b := Matrix([f1_coeffs_13,f2_coeffs_13,f4_coeffs_13]);
Determinant(M15b); // 2

// c65 + c65 + c65

M16 := Matrix([f1_coeffs_65,f2_coeffs_65,f3_coeffs_65]);
Determinant(M16); // ZERO, BUT:

M16b := Matrix([f1_coeffs_65,f2_coeffs_65,f4_coeffs_65]);
Determinant(M16b); // -2

// So we see that we have formal immersions at the same cusps as before mod 3
// Also for mod 2, we see that everything is 0 as before
// Also can see that 2 is the only issue here.
// Matches with the other case where by computing the factorisation of the non-zero dets,
// only 2*OK was appearing in the factorisation.
