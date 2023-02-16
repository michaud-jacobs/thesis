// Magma code to support the computations in the paper On some generalized Fermat equations of the form x^2 + y^2n = z^p by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/gen-fermat for all the code files and links to the paper

// The code works on Magma V2.26-10

// This code carries out the computations needed for the proof of Theorem 1.

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

