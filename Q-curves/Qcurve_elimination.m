// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.27-7.
// The code in this folder ("Q-curves") is based on joint work with Michael A Bennett and Samir Siksek.

// The code in this file carries out the elimination steps using Frey Q curves (and multi-Frey techniques).

// The output is in the file Qcurve_elimination_output.txt, available at:
// https://github.com/michaud-jacobs/thesis/blob/main/Q-curves/Qcurve_elimination_output.txt

////////////////////////////////////////////

q := 41; // Choose q = 17, 41, 89, or 97.
M<rootq> := QuadraticField(q);
OM :=Integers(M);

// start by defining gamma and gammab appropriately.

if q eq 17 then                    
   gamma := (-3+rootq)/2;
   gammab := (-3-rootq)/2;
end if;

if q eq 41 then 
   gamma := (-19 - 3*rootq)/2;
   gammab := (-19 + 3*rootq)/2;
end if;

if q eq 89 then
   gamma := (9+rootq)/2;
   gammab := (9-rootq)/2;
end if;

if q eq 97 then 
   gamma := (325+33*rootq)/2;
   gammab := (325-33*rootq)/2;
end if;

////////////////////////////////////////////////

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

// see output file (Qcurve_elimination_output.txt) for the output of the following loop.

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
