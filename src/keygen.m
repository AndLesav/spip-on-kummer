Keygen_uniform := function(size, dim: length_supp := 1)
    g := ZeroSequence(Rationals(), dim);
    Z := ZeroSequence(Rationals(), dim);
    S := {i : i in [1..dim]};
    T := RandomSubset(S, Ceiling(length_supp*dim));
    while g eq Z do
	g := Z;
	for i in T do
    	    g[i] := Random(-2^size, 2^size);
	end for;
    end while;
    return g;
end function;


Keygen_binom := function(p, n, dim: length_supp := 1)
    g := ZeroSequence(Rationals(), dim);
    Z := ZeroSequence(Rationals(), dim);
    S := {i : i in [1..dim]};
    T := RandomSubset(S, Ceiling(length_supp*dim));
    while g eq Z do
	for i in T do
	    s := 0;
	    for j in [1..n] do
		x := Random(1, Denominator(p));
		if x lt (Numerator(p)+1) then
		    s +:= 1;
		end if;
	    end for;
	    g[i] := s - (n div 2);
	end for;
    end while;
    return g;
end function;


KF_keygen_uniform := function(kummer_field, size/* : length_supp := dim */)
    basis := KF_primefree_basis(kummer_field[1], kummer_field[2]:list_primes := []);
    g := [];//ZeroSequence(Rationals(), dim);
    basis_r := KF_real_basis_embedding(basis, kummer_field[2], 100);
    for i in [1..#basis] do
	B := Round(Max(basis_r)*2^size/basis_r[i]);
	Append(~g, Rationals()!Random(-B, B));
    end for;
    return g;
end function;

Keygen := function(size, dim: length_supp := 1, shape:="uni", p:=1/2, n:=10, kum_field:=<>)
    if shape eq "uni" then
	return Keygen_uniform(size, dim: length_supp := length_supp);
    elif shape eq "binom" then
	return Keygen_binom(p, n, dim: length_supp := length_supp);
    elif shape eq "uniform" then
	return KF_keygen_uniform(kum_field, size);
    else
	return Keygen_uniform(0, dim: length_supp := 1);
    end if;
end function;


Relative_keygen_uniform := function(ground_field, extension, size/* : length_supp := dim */)
    g := [];//ZeroSequence(Rationals(), dim);
    ext_basis, ground_basis := Relative_primefree_basis(ground_field, extension);
    ext_basis := ext_basis[1];
    ground_basis := ground_basis[1];
    for i in [1..#ext_basis] do
	D_ext := Root(ext_basis[i], extension[2]);
	for j in [1..#ground_basis] do
	    D_ground := Root(ground_basis[j], ground_field[2]);
	    D := D_ext*D_ground;
	    B := Round(2^size/D);
	    Append(~g, Rationals()!Random(-B, B));
	end for;
    end for;
    return g;
end function;

/* create Log(h) = Log(g) + Log(u) with random u */
RandomGenLog := function(Lg, LU, precision, K: size:= 5)
    return RandomCosetRepresentative(Lg, LU: size:=size);
end function;


Bound_log_norm_key_kummer := function(kummer_field, size_key)
    dim := KF_dimension(kummer_field);
    g := [Rationals()!(2^size_key) : i in [1..dim]];
    B := KF_primefree_basis(kummer_field[1], kummer_field[2]);
    r := KF_real_embedding(g, kummer_field[1], kummer_field[2], 1000, B);
    return dim*Log(AbsoluteValue(r))^2;
end function;


Bound_log_norm_key_relative := function(ground_field, extension, size_key)
    dim := Relative_extension_dimension(ground_field, extension)[1];
    g := [Rationals()!(2^size_key) : i in [1..dim]];
    r := Relative_real_embedding(g, ground_field, extension, 1000);
    return dim*Log(AbsoluteValue(r))^2;
end function;


Log_enumeration_cost_kummer := function(U, size_key, kummer_field: B:=0, prune:=[])
    B := B;
    if B eq 0 then
	B := Bound_log_norm_key_kummer(kummer_field, size_key);
    end if;
    if #prune eq 0 then
	E := EnumerationCost(LogLattice_creation(U), B);
    else
	E := EnumerationCost(LogLattice_creation(U), B: Prune:=prune);
    end if;
    return E;
end function;



Log_enumeration_cost_relative := function(U, size_key, ground_field, extension: B:=0)
    B := B;
    if B eq 0 then
	B := Bound_log_norm_key_relative(ground_field, extension,size_key);
    end if;
    return EnumerationCost(LogLattice_creation(U), B);
end function;



KF_regulator := function(kummer_field, precision: U := [])
    V := U;
    if #V eq 0 then
	V := KF_units_real(kummer_field[1], kummer_field[2], precision, true/* : Units_List := Units_list */);
    end if;
    LV := Matrix([V[i,2] : i in [1..#V]]);
    LV := RowSubmatrixRange(LLL(LV), 1, Rank(LV));
    LV := Lattice(LV);
    return Sqrt(Determinant(LV));
end function;



Relative_regulator := function(Kg, Ke, precision: U := [])
    V := U;
    if #V eq 0 then
	V := Relative_units_real(Kg, Ke, precision);
    end if;
    LV := Matrix([V[i,2] : i in [1..#V]]);
    LV := RowSubmatrixRange(LLL(LV), 1, Rank(LV));
    LV := Lattice(LV);
    return Sqrt(Determinant(LV));
end function;


KF_regulator_simple := function(kummer_field, precision: U := [])
    V := U;
    if #V eq 0 then
	V := KF_simple_units(kummer_field[1], kummer_field[2], precision);
    end if;
    LV := LogLattice_creation(V);
    return Determinant(LV);
end function;
