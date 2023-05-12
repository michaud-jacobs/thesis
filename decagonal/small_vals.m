// Magma code to support the computations in my PhD thesis.

// We solve certain Thue equations arising in the cases p = 3, 5, and 7.

////////////////////////////////////////////

T<X> := PolynomialRing(Integers());

// Case 1: 3 does not divide n.

for p in [3,5,7] do
    f := 4*X^p -1;
    sols := Solutions(Thue(f),3); // Solutions to 4X^p-Y^p = 3
    assert #sols eq 1 and sols[1] eq [1,1]; // X = Y = 1 is the only solution
end for;

// Case 2: 3 fully divides n.

for p in [3,5,7] do
    f := 4*X^p -3^(p-2);
    sols := Solutions(Thue(f),1); // Solutions to 4X^p-3^(p-2)Y^p = 1
    if p eq 3 then
        assert #sols eq 1 and sols[1] eq [1,1]; // X = Y = 1 is the only solution
    else
        assert #sols eq 0; // No solutions
    end if;
end for;

// Case 3: 3^2 divides n.

for p in [3,5,7] do
    f := 4*(3^(p-2))*X^p -1;
    sols := Solutions(Thue(f),1); // Solutions to 4(3^(p-2))X^p-Y^p = 1
    assert #sols eq 1 and sols[1] eq [0,-1]; // X = 0, Y = -1 is the only solution
end for;
