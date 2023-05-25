// Magma code to support the computations in my PhD thesis.

// This code carries out certain computations for p-isogenies with p small

// The output is in the file "small_isog_output.txt", available at
// https://github.com/michaud-jacobs/thesis/blob/main/p-isogenies/small_isog_output.txt
// Some output is included within the file

////////////////////////////////////////////

// We start by considering the primes p = 11, 17, and 19 in each case
// This function verifies whether X_0(p)(K) has rank 0 or not
// In the case of positive rank, the function tries to construct an elliptic curve with a p-isogeny and good reduction (and therefore semistable reduction) at the primes of K above p

small_isog := function(d); // d is for the quadratic field K = Q(sqrt(d))
    print "Considering d =", d;
    K<a> := QuadraticField(d);
    OK := Integers(K);
    print "Class group exponent is", Exponent(ClassGroup(K));
    ranks := <>;
    for p in [11,17,19] do
        print "Doing p =", p;
        pfac := [Factorisation(p*OK)[i][1] : i in [1..#Factorisation(p*OK)]]; // primes above p
        X := SmallModularCurve(p); // the curve X_0(p) (over Q)
        XK := SmallModularCurve(p,K); // the curve X_0(p) over K
        // We check the rank using the quadratic twist of the curve by d
        Xd := QuadraticTwist(X,d);
        XdK := ChangeRing(Xd,K);
        _,phi := IsIsomorphic(XdK,XK); // isomorphism over K between twist and original curve

        Md,pid,tf1,tf2 := MordellWeilGroup(Xd: Effort := 3); // effort set to 3 to ensure a provably correct result.
        assert tf1 and tf2; // provably correct
        k := #Generators(Md);
        gen := Md.k; // will be an element of infinite order if the rank is positive

        if IsFinite(Md) then
            print "Rank is 0 over K";
            ranks := ranks cat <0>;
        else
            print "Positive rank over K";
            ranks := ranks cat <"pos">;
            i_range := [1,2,3,4,5,-1,-2,-3,-4,-5]; // we will test i*gen for i in this range
            for i in i_range do
                print "Doing i =", i;
                ptK := phi(XdK ! (pid(i*gen))); // point on X
                E := Domain(Isogeny(ptK,p)); // the corresponding elliptic curve
                if #pfac eq 1 then // unique prime above p
                    kod := LocalInformation(E,pfac[1])[5]; // reduction type
                    kod;
                else // there are two primes above p
                    kod1 := LocalInformation(E,pfac[1])[5];
                    kod2 := LocalInformation(E,pfac[2])[5];
                    <kod1, kod2>;
                end if;
                good_kod := KodairaSymbol("I0"); // The Kodaira symbol in the case of good reduction
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
    print "+++++++++++++++++++++++++++++++";
end for;

// The output is displayed in the "small_isog_output.txt" file

//////////////////////////////////////////////////////////////////

// Next, we consider the case d = -5 and p = 43

K<d> := QuadraticField(-5);
OK := Integers(K);

X := SmallModularCurve(43); // The curve X_0(43) (over Q)
XK := ChangeRing(X,K); // The curve X_0(43) over K
w := AtkinLehnerInvolution(X,43,43);
Xpl, phi := CurveQuotient(AutomorphismGroup(X, [w])); // This is X_0+(43)
Pts:=Points(Xpl: Bound := 100);
for Q in Pts do
    pbK := Points(ChangeRing(Pullback(phi,Q),K));
end for;

// by checking each pbK, we see that we obtain a non-Q-rational point over K in one case
// we define this point 'manually':

R := XK ! [1/3*(-2*d-2),4/3,1]; // the quadratic point we found
E1 := Domain(Isogeny(R,43)); // the corresponding elliptic curve

// we define the primes of K above 43
p1 := Factorisation(43*OK)[1][1]; 
p2 := Factorisation(43*OK)[2][1];

assert(Valuation(Conductor(E1),p1)) eq 2; // reduction is NOT semistable here for this curve
assert(Valuation(Conductor(E1),p2)) eq 0; 

// We now twist:

g := Generators(p1)[2];
E2 := QuadraticTwist(E1,g);
Factorisation(Integers() ! Norm(Conductor(E2)));
// Output: [ <2, 10>, <3, 4>, <11, 4> ], so good reduction at p1 and p2.
