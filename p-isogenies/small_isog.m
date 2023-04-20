// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.26-10

// This code carries out certain computations for p-isogenies with p small

// The output is in the file small_isog_output.txt, available at
// https://github.com/michaud-jacobs/thesis/blob/main/p-isogenies/small_isog_output.txt
// Some output is included within the file

////////////////////////////////////////////

// We start by considering the primes p = 11, 17, and 19 in each case
// This function verifies whether X_0(p)(K) has rank 0 or not
// In the case of positive rank, the function tries to construct an elliptic curve with a p-isogeny and good reduction (and therefore semistable reduction) at the primes of K above p

small_isog := function(d);
    print("Considering d = "),d;
    K<a> := QuadraticField(d);
    OK := Integers(K);
    print "Class group exponent is:", Exponent(ClassGroup(K));
    ranks := <>;
    for p in [11,17,19] do
        print("Doing p = "),p;

        pfac := [Factorisation(p*OK)[i][1] : i in [1..#Factorisation(p*OK)]];

        X := SmallModularCurve(p);
        XK := SmallModularCurve(p,K);

        Xd := QuadraticTwist(X,d);
        XdK := ChangeRing(Xd,K);
        _,phi := IsIsomorphic(XdK,XK);

        Md,pid,tf1,tf2 := MordellWeilGroup(Xd: Effort := 3); // can change effort.
        assert tf1 and tf2;
        k := #Generators(Md);
        gen := Md.k;

        if IsFinite(Md) then
            print("Rank is 0 over K");
            ranks := ranks cat <0>;
        else
            print("Positive rank over K");
            ranks := ranks cat <"pos">;
            i_range := [1,2,3,4,5,-1,-2,-3,-4,-5];
            for i in i_range do
                print("Doing i = "),i;
                ptK := phi(XdK ! (pid(i*gen)));
                E := Domain(Isogeny(ptK,p));
                if #pfac eq 1 then
                    kod := LocalInformation(E,pfac[1])[5];
                    kod;
                else
                    kod1 := LocalInformation(E,pfac[1])[5];
                    kod2 := LocalInformation(E,pfac[2])[5];
                    <kod1, kod2>;
                end if;
                good_kod := KodairaSymbol("I0");
                if (#pfac eq 1 and kod eq good_kod) or (#pfac eq 2 and kod1 eq good_kod and kod2 eq good_kod) then
                    print "Found a curve with good reduction at all primes above p";
                    break;
                end if;
                if i eq i_range[#i_range] then // Reached end of loop without success
                    print "Did not find a curve with good reduction at all primes above p. Check if semistable or increase range for i";
                end if;
            end for;
        end if;
    print "+++++++";
    end for;
    return ranks;
end function;

// We run the code for the following d:
for d in [-5] cat [2,3,5,6,7] cat [29,10,79,145,1756,697,1009] cat [47*67*101] do
    small_isog(d);
    print("+++++++++++++++++++++++++++++++");
end for;
// Output displayed at the end of this file.

//////////////////////////////////////////////////////////////////

// Next, we consider the case d = -5 and p = 43

K<d> := QuadraticField(-5);
OK := Integers(K);

X := SmallModularCurve(43);
XK := ChangeRing(X,K);
w := AtkinLehnerInvolution(X,43,43);
Xpl, phi := CurveQuotient(AutomorphismGroup(X, [w]));
Pts:=Points(Xpl: Bound := 100);
for Q in Pts do
    pbK := Points(ChangeRing(Pullback(phi,Q),K));
end for;

// we see that we obtain a non-Q-rational point over K in one case
// we define

R := XK ! [1/3*(-2*d-2),4/3,1];
E1 := Domain(Isogeny(R,43));

p1 := Factorisation(43*OK)[1][1];
p2 := Factorisation(43*OK)[2][1];

assert(Valuation(Conductor(E1),p1)) eq 2;
assert(Valuation(Conductor(E1),p2)) eq 0;

// We now twist:

g := Generators(p1)[2];
E2 := QuadraticTwist(E1,g);
Factorisation(Integers() ! Norm(Conductor(E2)));
// this is [ <2, 10>, <3, 4>, <11, 4> ], so good reduction at p1 and p2.

/* Output for d in [-5] cat [2,3,5,6,7] cat [47*67*101] cat [29,10,79] loop

Considering d =  -5
Class group exponent is: 2
Doing p =  11
Rank is 0 over K
+++++++
Doing p =  17
Rank is 0 over K
+++++++
Doing p =  19
Rank is 0 over K
+++++++
<0, 0, 0>
+++++++++++++++++++++++++++++++
Considering d =  2
Class group exponent is: 1
Doing p =  11
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Rank is 0 over K
+++++++
Doing p =  19
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
<"pos", 0, "pos">
+++++++++++++++++++++++++++++++
Considering d =  3
Class group exponent is: 1
Doing p =  11
Rank is 0 over K
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
<0, "pos", "pos">
+++++++++++++++++++++++++++++++
Considering d =  5
Class group exponent is: 1
Doing p =  11
Rank is 0 over K
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
IV
Doing i =  2
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Rank is 0 over K
+++++++
<0, "pos", 0>
+++++++++++++++++++++++++++++++
Considering d =  6
Class group exponent is: 1
Doing p =  11
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
IV
Doing i =  2
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Rank is 0 over K
+++++++
<"pos", "pos", 0>
+++++++++++++++++++++++++++++++
Considering d =  7
Class group exponent is: 1
Doing p =  11
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
IV
Doing i =  2
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Rank is 0 over K
+++++++
<"pos", "pos", 0>
+++++++++++++++++++++++++++++++
Considering d =  29
Class group exponent is: 1
Doing p =  11
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
<"pos", "pos", "pos">
+++++++++++++++++++++++++++++++
Considering d =  10
Class group exponent is: 2
Doing p =  11
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
IV
Doing i =  2
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
<"pos", "pos", "pos">
+++++++++++++++++++++++++++++++
Considering d =  79
Class group exponent is: 3
Doing p =  11
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
<"pos", "pos", "pos">
+++++++++++++++++++++++++++++++
Considering d =  145
Class group exponent is: 4
Doing p =  11
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
<IV, IV>
Doing i =  2
<I0, I0>
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
<"pos", "pos", "pos">
+++++++++++++++++++++++++++++++
Considering d =  1756
Class group exponent is: 5
Doing p =  11
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
<"pos", "pos", "pos">
+++++++++++++++++++++++++++++++
Considering d =  697
Class group exponent is: 6
Doing p =  11
Positive rank over K
Doing i =  1
<I0*, IV>
Doing i =  2
<II, III>
Doing i =  3
<III, II>
Doing i =  4
<IV, I0*>
Doing i =  5
<I0, I0>
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
<"pos", "pos", "pos">
+++++++++++++++++++++++++++++++
Considering d =  1009
Class group exponent is: 7
Doing p =  11
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Positive rank over K
Doing i =  1
IV
Doing i =  2
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  19
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
<"pos", "pos", "pos">
+++++++++++++++++++++++++++++++
Considering d =  318049
Class group exponent is: 122
Doing p =  11
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
Doing p =  17
Rank is 0 over K
+++++++
Doing p =  19
Positive rank over K
Doing i =  1
I0
Found a curve with good reduction at all primes above p
+++++++
<"pos", 0, "pos">
+++++++++++++++++++++++++++++++

*/
