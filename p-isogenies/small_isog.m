// Magma code to support the computations in the paper On elliptic curves with p-isogenies over quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/p-isog-quadratic for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is at the end of the file


// This code verifies the computations in part of the proof of Theorem 2, part of the proof of Proposition 5.5, and Remark 5.2

// We start by considering the primes p = 11, 17, and 19 in each case
// The code verifies whether X_0(p)(K) has rank 0 or not
// In the case of positive rank, the code tries to construct an elliptic curve with a p-isogeny which is semistable at the primes of K above p

small_isog := function(d);
    print("Considering d = "),d;
    K<a> := QuadraticField(d);
    OK := Integers(K);
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
        end if;

        if IsFinite(Md) eq false then 
            print("Positive rank over K");
            ranks := ranks cat <"pos">;
            if d lt 11 then 
               i_range := [1,2];
            
            else i_range := [1]; 
            end if;
            for i in i_range do  
                print("Doing i = "),i;
                ptK := phi(XdK ! (pid(i*gen)));
                E := Domain(Isogeny(ptK,p));
                for pp in pfac do
                    LocalInformation(E,pp)[5]; // the Kodaira symbol, I0 means good reduction
                end for;
            end for;
        end if; 
    end for;
    return ranks, ClassNumber(K);
end function;

// We run the code for the following d:
for d in [-5] cat [2,3,5,6,7] cat [47*67*101] cat [29,10,79] do
    small_isog(d);
    print("++++++++++++++++");
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
Factorisation(Integers() ! Norm(Conductor(E2))); // this is [ <2, 10>, <3, 4>, <11, 4> ], so good reduction at p1 and p2.

/* Output for d in [-5] cat [2,3,5,6,7] cat [47*67*101] cat [29,10,79] 

Considering d =  -5
Doing p =  11
Rank is 0 over K
Doing p =  17
Rank is 0 over K
Doing p =  19
Rank is 0 over K
<0, 0, 0> 2

Considering d =  2
Doing p =  11
Positive rank over K
Doing i =  1
I0
Doing i =  2
I0
Doing p =  17
Rank is 0 over K
Doing p =  19
Positive rank over K
Doing i =  1
I0
Doing i =  2
I0
<"pos", 0, "pos"> 1

Considering d =  3
Doing p =  11
Rank is 0 over K
Doing p =  17
Positive rank over K
Doing i =  1
I0
Doing i =  2
I0
Doing p =  19
Positive rank over K
Doing i =  1
I0
Doing i =  2
I0
<0, "pos", "pos"> 1

Considering d =  5
Doing p =  11
Rank is 0 over K
Doing p =  17
Positive rank over K
Doing i =  1
IV
Doing i =  2
I0
Doing p =  19
Rank is 0 over K
<0, "pos", 0> 1

Considering d =  6
Doing p =  11
Positive rank over K
Doing i =  1
I0
Doing i =  2
I0
Doing p =  17
Positive rank over K
Doing i =  1
IV
Doing i =  2
I0
Doing p =  19
Rank is 0 over K
<"pos", "pos", 0> 1

Considering d =  7
Doing p =  11
Positive rank over K
Doing i =  1
I0
Doing i =  2
I0
Doing p =  17
Positive rank over K
Doing i =  1
I0
Doing i =  2
I0
Doing p =  19
Rank is 0 over K
<"pos", "pos", 0> 1

Considering d =  318049
Doing p =  11
Positive rank over K
Doing i =  1
I0
Doing p =  17
Rank is 0 over K
Doing p =  19
Positive rank over K
Doing i =  1
I0
<"pos", 0, "pos"> 122

Considering d =  29
Doing p =  11
Positive rank over K
Doing i =  1
I0
Doing p =  17
Positive rank over K
Doing i =  1
I0
Doing p =  19
Positive rank over K
Doing i =  1
I0
<"pos", "pos", "pos"> 1

Considering d =  10
Doing p =  11
Positive rank over K
Doing i =  1
I0
Doing i =  2
I0
Doing p =  17
Positive rank over K
Doing i =  1
I0
Doing i =  2
I0
Doing p =  19
Positive rank over K
Doing i =  1
I0
Doing i =  2
I1*
<"pos", "pos", "pos"> 2

Considering d =  79
Doing p =  11
Positive rank over K
Doing i =  1
I0
Doing p =  17
Positive rank over K
Doing i =  1
I0
Doing p =  19
Positive rank over K
Doing i =  1
I0
<"pos", "pos", "pos"> 3

*/

 
     
