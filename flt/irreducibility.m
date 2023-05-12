// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.27-7

// The code in this file carries out the irreducibility checks.

// The code uses the function "non_const" from the file "non_constant_sig.m" available in the "p-isogenies" folder of this thesis' repository at:
// https://github.com/michaud-jacobs/thesis/blob/main/p-isogenies/non_constant_sig.m

load "../p-isogenies/non_constant_sig.m";

////////////////////////////////////////////

// We first consider the case of a non-constant isogeny signature:

D := [d : d in [26..97] | IsSquarefree(d)];
for d in D do
    bad_p := non_const(d: t := 4, aux_upper_bd := 50);
    assert bad_p eq {2,3,5,7,11,13,17,19,37};
end for;

// We now consider the case in which p ramifies in K.
// For the pairs (d,p) = (61,61) and (89,89) it is enough to contruct primes of multiplicative reduction:

// We use the following function:

// Input: d, p, bd (a search bound)
// Output: A list of primes
// Each prime splits in K = Q(sqrt_d) and the two primes of K above it are of multiplicative reduction for E_{a,b,c,p,d}

mult_primes_q := function(d,p,bd);
    U<x>:=PolynomialRing(Rationals());
    K := QuadraticField(d);
    OK:=Integers(K);
    qs:= [ n*p+1: n in [1..bd] | (IsPrime(n*p+1)) and (IsSplit(n*p+1,OK)) and  ( (Integers() ! (Resultant(x^n-1,(x+1)^n-1)) mod (n*p+1)) ne 0  ) ];
    return qs;
end function;

for d in [61, 89] do
    p := d;
    bd := 50;
    print mult_primes_q(d,p,bd);
end for;

/* Output:
[ 977, 1709, 2441 ]
[ 179, 3917, 4451 ]
*/

// We see that we were successful in finding primes of multiplicative reduction
