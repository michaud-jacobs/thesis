// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.26-10

// The code in this computes constants for p = 11, 13, 17 for the asymptotic version for signature (2, 2n, 3p)

// The output is contained within the file

////////////////////////////////////////////

// Computing B_p
// The integer B_p is defined in the paper:
// F. Freitas and S. Siksek. Criteria for irreducibility of mod p representations of Frey curves. J. Théor. Nombres Bordeaux, 27(1):67–76, 2015
// The code works for any prime p.

for p in [11,13,17] do
    print "Computing B-value for p =", p;
    L<zet>:=CyclotomicField(p);
    K<t>:=sub<L | zet+1/zet>; 
    OK:=Integers(K); 

    Aut,_,nu:=AutomorphismGroup(K);

    Gal:=[nu(Aut.1)^i : i in [0..((p-1)/2)-1]]; // elements of Gal(K/Q)

    UK,psi:=UnitGroup(K);
    r:=#Generators(UK);
    es:=[K ! (psi(UK.i)) : i in [1..r]];    // basis for unit group

    S:=[];                      // we compute the possible non-constant isogeny characters
    for i in [1..2^r-2] do
        seq1:=Intseq(i,2);
        seq2:=seq1 cat [0*j : j in [1..r-#seq1]];
        seq:=[12*ss : ss in seq2];
        S:=S cat [seq];
    end for;

    Ns:=[];          // we compute the twisted norms
    for j in [1..r] do
        Nsjs:=[];
        for s in S do
            Nsjs := Nsjs cat [  &* [ (Gal[i](es[j]))^s[i] : i in [1..r]]  ];
        end for;
        Ns:=Ns cat [Nsjs];
    end for;


    As_s:=[];                // we compute the A_s values
    for j in [1..2^r-2] do
        I:=&+[(Ns[i][j]-1)*OK : i in [1..r]];
        if I eq 0*OK then
            As:=0;
            As_s:=As_s cat [As];
        else  As:=Integers() ! Norm(I);
            As_s:=As_s cat [As];
        end if;
    end for;

    B:=LCM(As_s);        // the required value B.
    print "B is", Factorisation(B);
    print "++++++++++++++++++++++++++";
end for;

/* Output:

Computing B-value for p = 11
B is []
++++++++++++++++++++++++++
Computing B-value for p = 13
B is [ <2, 18>, <3, 12>, <5, 6>, <13, 3> ]
++++++++++++++++++++++++++
Computing B-value for p = 17
B is [ <2, 32>, <5, 8>, <13, 8>, <17, 4>, <67, 8> ]
++++++++++++++++++++++++++

*/

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

// Dimensions of space of Hilbert cusp forms new at level N_l

for p in [11,13,17] do
    L<zet>:=CyclotomicField(p);
    K:=sub<L | zet+1/zet>; 
    OK:=Integers(K);
    H:=HilbertCuspForms(K,2^3*OK);
    Hnew:=NewSubspace(H);
    dim := Dimension(Hnew); // a few minutes for p=13 and p=17.
    print "Dimension is", dim, "for p =", p;
end for;

/* Output:

Dimension is 1201 for p = 11
Dimension is 31422 for p = 13
Dimension is 41883752 for p = 17

*/
