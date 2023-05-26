// Magma code to support the computations in my PhD thesis.

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

////////////////////////////////////////////

// We now consider the case in which p ramifies in K.
// If 2 ramifies in K then we may argue as the thesis
// All quadratic points on the following curves are defined over imaginary quadratic fields:
// X_0(34), X_0(38), X_0(92), X_0(62), X_0(73), X_0(97)
// So we immediately remove the primes 17, 19, 23, 31, 73, 97
// We isolate the remaining pairs (d,p):

ram_pairs := []; // build up to list of pairs (d,p) to consider
for d in D do
    K := QuadraticField(d);
    OK := Integers(K);
    DK := Discriminant(OK);
    rams := PrimeFactors(DK);
    for p in rams do 
        if p eq 2 then 
            continue; // use argument provided in thesis to rule out all p
        elif p ge 17 and p notin [17,19,23,31,73,97] then  
            ram_pairs := ram_pairs cat [<d,p>];
        end if;
    end for;
end for;

ram_pairs; 
/* Output:
[ 
<29, 29>, <37, 37>, <41, 41>, <43, 43>, <47, 47>, <53, 53>, <58, 29>, <59, 59>, <61, 61>, <67, 67>, 
<71, 71>, <74, 37>, <79, 79>, <82, 41>, <83, 83>, <86, 43>, <87, 29>, <89, 89>, <94, 47> 
]
*/

// For each of these pairs (d,p), it is enough to contruct primes of multiplicative reduction:

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

for pair in ram_pairs do
    d := pair[1];
    p := pair[2];
    bd := 50;
    print pair, mult_primes_q(d,p,bd);
end for;

/* Output:
<29, 29> [ 59, 233, 929, 1103, 1277, 1451 ]
<37, 37> [ 149, 593, 1259, 1481 ]
<41, 41> [ 83, 821, 1559 ]
<43, 43> [ 173, 1721 ]
<47, 47> [ 941, 2069 ]
<53, 53> [ 107, 743, 1061, 1697 ]
<58, 29> [ 233, 929, 1103 ]
<59, 59> [ 1181, 1889 ]
<61, 61> [ 977, 1709, 2441 ]
<67, 67> [ 269, 1877 ]
<71, 71> [ 569, 2273 ]
<74, 37> [ 593, 1481 ]
<79, 79> [ 317, 2213 ]
<82, 41> [ 1559 ]
<83, 83> [ 2657 ]
<86, 43> [ 947, 1721, 1979 ]
<87, 29> [ 59, 1103, 1451 ]
<89, 89> [ 179, 3917, 4451 ]
<94, 47> [ 659, 1787 ]
*/

// We see that we were successful in finding primes of multiplicative reduction in each case
