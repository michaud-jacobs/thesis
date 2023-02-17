// Magma code to support the computations in my PhD thesis.
// The code works on Magma V2.26-10

// The code in this computes the Hilbert cusp form decomposition for signature (2, 2n, 21)
// The output is contained within the file

////////////////////////////////////////////

p:=7;
L<zet>:=CyclotomicField(p);
K:=sub<L | zet+1/zet>;
OK:=Integers(K);

q:=3*OK; // The unique prime of K above 3.
nq:=Norm(q);

H:=HilbertCuspForms(K,2^3*OK); 
Hnew:=NewSubspace(H);
Dimension(Hnew);   // 5
NewformDecomposition(Hnew); // 5 forms

