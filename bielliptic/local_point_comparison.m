// Magma code to support the computations in my PhD thesis.

// The code in this file verifies the example computations with the local points on twist method

////////////////////////////////////////////

// The following function takes as input a prime p and a squarefree integer d
// It outputs 0 or 1

// 0 means that the twisted curve X_0(p)^(d) may have a rational point
// 1 means that the twisted curve X_0(p)^(d) does not have a rational point

// The function implements parts of Theorem 1.1 of:
// E. Ozman. Points on quadratic twists of X_0(N). Acta Arith., 152(4):323-348, 2012.

local_point_check := function(p,d);
    loc := 0; // a flag
    K := QuadraticField(d);
    OK := Integers(K);
    DOK := Discriminant(OK);

    M := QuadraticField(-p);
    OM := Integers(M);
    DOM := Discriminant(OM);

    ls := [l : l in PrimeFactors(DOK) | IsZero(DOM mod l) eq false];
    for l in ls do
        ll := Factorisation(l*OM)[1][1];
        if IsPrincipal(ll) eq false then // ideal is principal if and only if totally split in Hilbert class field
            loc := 1;
            return loc;
        end if;
    end for;
    D := Discriminant(EquationOrder(M));
    B := NumberField(HilbertClassPolynomial(D)); // This is the ring class field of the order O. It is also Q(j(O)). 
    OB := Integers(B);
    for l in ls do
        fac := Factorisation(l*OB);
        norms_l := [Norm(ll[1]) : ll in fac ]; // We check the inertia degrees
        if l notin norms_l then
            loc := 1;
            return loc;
        end if;
    end for;
    return loc;
end function;


// We test for which values of d the function succeeds when p = 53

D0 := [d : d in [-100..100] | d ne 0 and d ne 1 and IsSquarefree(d)];
D := [d : d in D0 | d notin [-43, -7, -11 , -1]]; // Discard ds for which sieve fails
assert #D eq 117;

success_ct := 0;
for d in D do
    success_ct := success_ct + local_point_check(53,d);
end for;

assert success_ct eq 94; // succeeded for 94 values.
