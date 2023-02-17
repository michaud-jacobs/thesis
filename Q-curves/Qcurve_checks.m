// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.27-7.
// The code in this folder ("Q-curves") is based on joint work with Michael A Bennett and Samir Siksek.

// The code in this file carries out basic checks on the Frey Q-curves.

////////////////////////////////////////////

q := 41; // Choose q = 17, 41, 89, or 97.
M<rootq> := QuadraticField(q);
OM :=Integers(M);

// start by defining gamma and gammab appropriately and check they satisfy requirements.

if q eq 17 then                    
   gamma := (-3+rootq)/2;
   gammab := (-3-rootq)/2;
   assert gamma*gammab eq -2;
   _,red := quo<OM | gamma^2>;
   assert IsZero(red(rootq+1));
   assert IsZero(red(gammab+1));
   fac1 := Factorisation(2*OM)[1][1];
   fac2 := Factorisation(2*OM)[2][1];
   assert gamma*OM eq fac1;
   assert gammab*OM eq fac2;
end if;

if q eq 41 then 
   //delta := 32 + 5*rootq;
   //deltab:= 32 - 5*rootq;
   gamma := (-19 - 3*rootq)/2;
   gammab := (-19 + 3*rootq)/2;
   assert gamma*gammab eq -2;
   _,red := quo<OM | gamma^2>;
   assert IsZero(red(rootq+1));
   assert IsZero(red(gammab+1));
   fac1 := Factorisation(2*OM)[1][1];
   fac2 := Factorisation(2*OM)[2][1];
   assert gamma*OM eq fac1;
   assert gammab*OM eq fac2;
end if;

if q eq 89 then
   //delta := 500 + 53*rootq;
   //deltab := 500 - 53*rootq;
   gamma := (9+rootq)/2;
   gammab := (9-rootq)/2;
   assert gamma*gammab eq -2;
   _,red := quo<OM | gamma^2>;
   assert IsZero(red(rootq+1));
   assert IsZero(red(gammab+1));
   fac1 := Factorisation(2*OM)[1][1];
   fac2 := Factorisation(2*OM)[2][1];
   assert gamma*OM eq fac1;
   assert gammab*OM eq fac2;
end if;

if q eq 97 then 
   delta := 5604 + 569*rootq;
   deltab := 5604 - 569*rootq;
   gamma := (325+33*rootq)/2;
   gammab := (325-33*rootq)/2;
   assert gamma*gammab eq -2;
   _,red := quo<OM | gamma^2>;
   assert IsZero(red(rootq+1));
   assert IsZero(red(gammab+1));
   fac1 := Factorisation(2*OM)[1][1];
   fac2 := Factorisation(2*OM)[2][1];
   assert gamma*OM eq fac1;
   assert gammab*OM eq fac2;
end if;

////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////  

// We verify the computation that c(sigma, sigma) = -2.

aff<A,w,wb,gam,gamb>:=AffineSpace(Rationals(),5);  // Here, A is q^{m+1}
S:=Scheme(aff,[w+wb-A^2, gam*gamb+2]);
FF:=FieldOfFractions(CoordinateRing(S));
A:=FF!A;
w:=FF!w;
wb:=FF!wb;
gam:=FF!gam;
gamb:=FF!gamb;

E := EllipticCurve( [ 0 , 2*gam*A , 0 , gam^2*w , 0 ]);
Econj := EllipticCurve( [ 0 , 2*gamb*A, 0, gamb^2*wb , 0 ]);

// We define the map phi_sigma
_<x,y>:=FunctionField(Econj);
phi := map<  Econj -> E | [ 	(x^2 + 2*gamb*A*x + gamb^2*wb)/(gamb^2*x), (x^2 -gamb^2*wb)*y/(gamb^3*x^2), 1] >;

// We define the map sigma((phi_sigma))
_<x,y>:=FunctionField(E);
sigphi := map<  E -> Econj | [ 	(x^2 + 2*A*gam*x + gam^2*w)/(gam^2*x), (x^2 -gam^2*w)*y/(gam^3*x^2), 1] >;  

// Want to evaluate phi circ sigma(phi).
// This is sigma(phi) * phi in Magma notation!

Phi:=sigphi*phi;
assert Domain(Phi) eq E and Codomain(Phi) eq E;

Theta:=map<E -> E | DefiningEquations(MultiplicationByMMap(E,-2))>;

assert Phi eq Theta; // Therefore phi circ sigma(phi) = -2.
