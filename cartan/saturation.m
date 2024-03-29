// Magma code to support the computations in my PhD thesis.

// The code in this file concerns the saturation step

// The output is in the file "saturation_output.txt", available at
// https://github.com/michaud-jacobs/thesis/blob/main/cartan/saturation_output.txt

// The code uses data from the file "eqn_data.m" available at:
// https://github.com/michaud-jacobs/thesis/blob/main/cartan/eqn_data.m

load "eqn_data.m";

////////////////////////////////////////////

C := Curve(ProjectiveSpace(S), eqn_X_plus); //  The curve X_ns^+(13) 

// This function takes as input a prime l and a sequence of auxiliary primes aux_p = [p_1, ... , p_n]
// It tries to prove that the index in question is not divisible by l
// See the functions below for help choosing the primes in aux_p

saturation_test := function(l,aux_p);    
    Zl3:=AbelianGroup([l,l,l]); 
    Int_Kp := Zl3;   // Initial intersection is the whole of (Z/lZ)^3
    Kps:=[];  // sequence of kernels of the maps pi_p
    Int_Kp_sizes := [];  // sequence of sizes of intersections of kernels     
    for p in aux_p do   
        print "Using auxiliary prime p =", p;                                               
        Cp:=ChangeRing(C,GF(p)); 
        assert IsNonsingular(Cp);          
        ClGrp,phi,psi:=ClassGroup(Cp);
        Z:=FreeAbelianGroup(1);
        degr:=hom<ClGrp->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(ClGrp)]>;  
        JFp:=Kernel(degr);                 // Jacobian mod p as an abelian group
        JFpmodl,pi:=quo<JFp | l*JFp>;      // J(F_p) / l*J(F_p)
    
        Del_1 := psi(Place(Cp ! [0,1,0])  - Place(Cp ! [1,0,0]));
        Del_2 := psi(Place(Cp ! [0,0,1])  - Place(Cp ! [1,0,0]));
        Del_3 := psi(Place(Cp ! [-1,0,1]) - Place(Cp ! [1,0,0]));  // Generators for the group G^+ mod p

        pi_p:=hom<Zl3->JFpmodl | [pi(Del_1),pi(Del_2),pi(Del_3)]>; // The map pi_p
        Kp:=Kernel(pi_p);
        Kps:=Kps cat [Kp];
        Int_Kp := Int_Kp meet Kp;
        Int_Kp_sizes := Int_Kp_sizes cat [#Int_Kp];
        print "Int_Kp has size", #Int_Kp;
        print "+++++++++";
        if #Int_Kp eq 1 then 
            print "++++++++++++++++++++++++++++++++";
            print "Index not divisible by", l;
            break;
        end if;
    end for;

    if #Int_Kp ne 1 then 
        print "++++++++++++++++++++++++++++++++";
        print "Index may be divisible by", l;          
    end if;

    print "Intersection sizes are", Int_Kp_sizes;
    return #Int_Kp;    
end function;

//////////////////////////////////////////////////////////////////////////////////////////

// Given l, we choose primes p such that l divides #J(F_p)
// We first compute the exponent of J(F_p) for all primes p < 500 with p not 13.

// The code below produces the Jacobian data (JFp_data) present in the eqn_data.m file
// Runtime: it takes some time to run, so it is commented out
/*
JFp_data_copy := [];
for n in [1..500] do
    if IsPrime(n) eq false or n eq 13 then 
        JFp_data_copy := JFp_data_copy cat [<n,1>];  // 1 in data if not applicable
        continue;
    end if;
    p := n;
    Cp:=ChangeRing(C,GF(p)); 
    assert IsNonsingular(Cp);          
    ClGrp,phi,psi:=ClassGroup(Cp);
    Z:=FreeAbelianGroup(1);
    degr:=hom<ClGrp->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(ClGrp)]>;  
    JFp:=Kernel(degr); // Jacobian mod p
    JFp_data_copy := JFp_data_copy cat [<p,LCM([Order(ee) : ee in Generators(JFp)])>];
end for;
assert JFp_data_copy eq JFp_data;
*/

//////////////////////////////////

// The following function chooses auxiliary primes for a given l, using the data computed above

aux_prime_chooser := function(l,JFp_data);
    aux := [];
    for p in PrimesInInterval(2,#JFp_data) do
        if (JFp_data[p][2] mod l) eq 0 then // We check if p is a suitable prime
            aux := aux cat [p];   // if it is, then we include it
        end if;
    end for;
    return aux;
end function;

//////////////////////////////////////////////////////////////////////////////////////////

// We now prove that the index is not divisible by the primes l in ls_to_test defined below
// The output is available in the file "saturation_output.txt" 

ls_to_test := [3,5,13,29];

for l in ls_to_test do
    print "Testing saturation for l =", l;
    print "Choosing auxiliary primes";
    aux_p := aux_prime_chooser(l,JFp_data);
    print "Auxiliary primes are", aux_p;
    print "+++++++++";
    _ := saturation_test(l, aux_p);
    print "===========================================";
end for;
