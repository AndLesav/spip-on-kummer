// hamming weight of sequence and support
MC_weight := function(x)
    w := 0; s := [];
    for i in [1..#x] do
	if (x[i] ne 0) then
	    w := w + 1;
	    Append(~s, i);
	end if;
    end for;
    return w, s;
end function;


/* action of morphism beta on index */
Galois_action_index := function(beta, index, field_exponent)
    alpha := IndexToExponent(index, #beta, field_exponent);
    return IntegerRing()!InnerProduct(ChangeRing(Vector(beta), GF(field_exponent)), ChangeRing(Vector(alpha), GF(field_exponent)));
end function;



/* action of morphism defined by sigma_1, sigma_2 on basis element of index I --- relative version */
Relative_galois_action_index := function(sigma, index, ground_field, extension)
    I := Absolute_to_relative_index(index, ground_field, extension);
    return [Galois_action_index(sigma[1], I[2], ground_field[2]), Galois_action_index(sigma[2], I[1], extension[2])];
end function;


/* action of morphism beta on basis elements */
Galois_action_basis := function(beta, field_sequence, field_exponent)
    action := [];
    for i in [1..field_exponent^#field_sequence] do
	Append(~action, Galois_action_index(beta, i, field_exponent));
    end for;
    return action;
end function;


/* action of sigma on basis */
Relative_galois_action_basis := function(sigma, ground_field, extension)
    field_dim := ground_field[2]^#ground_field[1]*extension[2]^#extension[1];
    action := [];
    for i in [1..field_dim] do
	Append(~action, Relative_galois_action_index(sigma, i, ground_field, extension));
    end for;
    return action;
end function;


/* action of morphism beta on basis elements of Galois closure */
Galois_action_closure := function(beta, field_sequence, field_exponent)
    action := Galois_action_basis(beta, field_sequence, field_exponent);
    A := [];
    for i in [1..field_exponent-1] do
	Append(~A, [(action[j] + (i-1)) mod field_exponent : j in [1..#action]]); 
    end for;
    return A;
end function;



/* image of f in K(zeta_p) under morphism beta */
Galois_morphism_closure := function(f, beta, field_sequence, field_exponent)
    field_dim := field_exponent^#field_sequence;    
    N := (field_exponent-1)*field_dim;
    Z := ZeroSequence(Rationals(), N);
    g := Z;
    Z := Vector_to_tower(Z, field_exponent-1);
    if #f eq field_dim then
	for i in [1..#f] do
	    g[i] := f[i];
	end for;
	g := Vector_to_tower(g, field_exponent-1);
    else
	g := Vector_to_tower(f, field_exponent-1);
    end if;
    action := Galois_action_closure(beta, field_sequence, field_exponent);
    for i in [1..field_exponent-1] do
	for j in [1..field_dim] do
	    if action[i, j] ne (field_exponent-1) then
		Z[1+action[i,j], j] := Z[1+action[i,j], j] + g[i, j];
	    else
		for s in [1..field_exponent-1] do
		    Z[s, j] := Z[s, j] - g[i,j];
		end for;
	    end if;
	end for;
    end for;
    return &cat Z;
end function;


/* image of f in K(zeta_p) under morphism beta */
Relative_galois_morphism_closure := function(f, sigma, ground_field, extension)
    dimension := Relative_extension_dimension(ground_field, extension);
    field_dim := dimension[1];
    ext_dim := dimension[2];
    ground_dim := dimension[3];
    galois_dim := (ground_field[2]-1)*(extension[2]-1)*field_dim;
    Z := ZeroSequence(Rationals(), galois_dim);
    g := Z;
    Z := Absolute_to_relative_dim(Z, extension[2]-1);
    if #f eq field_dim then
	for i in [1..#f] do
	    g[i] := f[i];
	end for;
	g := Absolute_to_relative_dim(g, extension[2]-1);
    else
	g := Absolute_to_relative_dim(f, extension[2]-1);
    end if;
    g := [Absolute_to_relative_dim(g[i], ground_field[2]-1) : i in [1..#g]];
    Z := [Absolute_to_relative_dim(Z[i], ground_field[2]-1) : i in [1..#g]];
    Z1 := [];
    h := [];
    for i in [1..#g] do
	Append(~h, [Absolute_to_relative_dim(g[i, j], ext_dim) : j in [1..#g[i]]]);
	Append(~Z1, [Absolute_to_relative_dim(Z[i, j], ext_dim) : j in [1..#g[i]]]);
    end for;
    Z := Z1;
    g := h;
    action := Galois_action_closure(sigma[2], extension[1], extension[2]);
    for i in [1..extension[2]-1] do
	for k in [1..ground_field[2]-1] do
	    for j in [1..ext_dim] do
		if action[i, j] ne (extension[2]-1) then
		    Z[1+action[i,j], k, j] := ElementToSequence(Vector(Z[1+action[i,j], k, j]) + Vector(g[i, k, j]));
		else
		    for s in [1..extension[2]-1] do
			Z[s, k, j] := ElementToSequence(Vector(Z[s, k, j]) - Vector(g[i, k, j]));
		    end for;
		end if;
	    end for;
	end for;
    end for;
    for i in [1..extension[2]-1] do
	for j in [1..ext_dim] do
	    h := &cat [Z[i][k][j] : k in [1..ground_field[2]-1]];
            h := Galois_morphism_closure(h, sigma[1], ground_field[1], ground_field[2]);
	    h := Absolute_to_relative_dim(h, ground_field[2]-1);
	    for k in [1..ground_field[2]-1] do
		Z[i,k,j] := h[k];
	    end for;
	end for;
    end for;
    return &cat &cat &cat Z;
end function;



/* minkowski embedding of x : return elements in K(zeta) */
Minkowski_embedding := function(x, field_sequence, field_exponent)
    V := VectorSpace(GF(field_exponent), #field_sequence);
    mink := [];
    for beta in V do
	Append(~mink, Galois_morphism_closure(x, ChangeUniverse(ElementToSequence(beta), Integers()), field_sequence, field_exponent));
    end for;
    return mink;
end function;



/* image of family F of elements of K(zeta_p) under morphism beta */
Galois_morphism_closure_family := function(F, beta, field_sequence, field_exponent)
    field_dim := field_exponent^#field_sequence;    
    N := (field_exponent-1)*field_exponent^#field_sequence;
    action := Galois_action_closure(beta, field_sequence, field_exponent);
    G := [];
    for t := 1 to #F do
	f := F[t];
	Z := ZeroSequence(Rationals(), N);
	g := Z;
	Z := Vector_to_tower(Z, field_exponent-1);
	if #f eq field_exponent^(#field_sequence) then
	    for i in [1..#f] do
		g[i] := f[i];
	    end for;
	    g := Vector_to_tower(g, field_exponent-1);
	else
	    g := Vector_to_tower(f, field_exponent-1);
	end if;
	for i in [1..field_exponent-1] do
	    for j in [1..field_dim] do
		if action[i, j] ne (field_exponent-1) then
		    Z[1+action[i,j], j] := Z[1+action[i,j], j] + g[i, j];
		else
		    for s in [1..field_exponent-1] do
			Z[s, j] := Z[s, j] - g[i,j];
		    end for;
		end if;
	    end for;
	end for;
	Append(~G, &cat Z);
    end for;
    return G;
end function;


Relative_galois_closure_morphism_family := function(F, sigma, ground_field, extension);
    G := [];
    for i in [1..#F] do
	Append(~G, Relative_galois_morphism_closure(F[i], sigma, ground_field, extension));
    end for;
    return G;
end function;


/* multiplication of y in Galois closure by element x in K */
Galois_closure_mult_scalar := function(x, y, field_sequence, field_exponent)
    g := Vector_to_tower(y, field_exponent-1);
    K := KF_creation(field_sequence, field_exponent);
    g := Vector([Vector_to_NFelement1(g[i], field_sequence, field_exponent:KF:=K) : i in [1..#g]]);
    g *:= Vector_to_NFelement1(x, field_sequence, field_exponent:KF:=K);
    g := ElementToSequence(g);
    g := [NFelement_to_vector1(g[i], field_sequence, field_exponent) : i in [1..#g]];
    return &cat g;
end function;



/* multiplication of family F in Galois closure by element x in K */
Galois_closure_mult_scalar_family := function(x, F, field_sequence, field_exponent)
    G := [];
    K := KF_creation(field_sequence, field_exponent);
    a := Vector_to_NFelement1(x, field_sequence, field_exponent:KF:=K);
    for j in [1..#F] do
	g := Vector_to_tower(F[j], field_exponent-1);
	g := Vector([Vector_to_NFelement1(g[i], field_sequence, field_exponent:KF:=K) : i in [1..#g]]);
	g *:= a;
	g := ElementToSequence(g);
	g := [NFelement_to_vector1(g[i], field_sequence, field_exponent) : i in [1..#g]];
	Append(~G, &cat g);
    end for;
    return G;
end function;


/* multiplication of family F in Galois closure by element x in K --- relative version */
Relative_galois_closure_mult_scalar_family := function(x, F, ground_field, extension)
    G := [];
    K := Relative_extension_creation(ground_field, extension);
    a := Relative_vector_to_NFelement1(x, ground_field, extension:KE:=K);
    for j in [1..#F] do
	g := Absolute_to_relative_dim(F[j], (ground_field[2]-1)*(extension[2]-1));
	g := Vector([Relative_vector_to_NFelement1(g[i], ground_field, extension:KE:=K) : i in [1..#g]]);
	g *:= a;
	g := ElementToSequence(g);
	g := [Relative_NFelement_to_vector1(g[i], ground_field, extension) : i in [1..#g]];
	Append(~G, &cat g);
    end for;
    return G;
end function;



/* calculate product of f*g element of galois closure of K */
Galois_closure_multiplication := function(f, g, field_sequence, field_exponent)
    K := KF_creation(field_sequence, field_exponent);
    if field_exponent ne 2 then    
	P<x> := PolynomialRing(Integers());
	pol := &+[ x^i : i in [0..field_exponent-1]];
	L<zeta> := ext< K | pol :Check:=false>;
	a := Vector_to_tower(f, field_exponent-1);
	b := Vector_to_tower(g, field_exponent-1);
	a := [Vector_to_NFelement1(a[i], field_sequence, field_exponent:KF:=K) : i in [1..#a]];
	b := [Vector_to_NFelement1(b[i], field_sequence, field_exponent:KF:=K) : i in [1..#b]];
	a := L!a;
	b := L!b;
	a := [NFelement_to_vector1(ElementToSequence(a*b)[i], field_sequence, field_exponent) : i in [1..field_exponent-1]];
	return &cat a;
    else
	return NFelement_to_vector1(Vector_to_NFelement1(f, field_sequence, field_exponent: KF:=K)*Vector_to_NFelement1(g,field_sequence, field_exponent: KF:=K), field_sequence, field_exponent);
    end if;
end function;


/* calculate product of f*g element of galois closure of K */
/* there are several case because of multiquadratic extensions */
Relative_galois_closure_multiplication := function(f, g, ground_field, extension)
    P<x> := PolynomialRing(Integers());
    K := Relative_extension_creation(ground_field, extension);
    /* first none are multiquadratics */
    if (ground_field[2] ne 2) and (extension[2] ne 2) then
	pol_ground := &+ [x^i : i in [0..ground_field[2]-1]];
	L<zeta_ground> := ext< K | pol_ground :Check:=false>;
	pol_ext := &+ [x^i : i in [0..extension[2]-1]];
	G<zeta_ext> := ext< L | pol_ext :Check:=false>;
	a := Absolute_to_relative_dim(f, extension[2]-1);
	b := Absolute_to_relative_dim(g, extension[2]-1);
	a := [Absolute_to_relative_dim(a[i], ground_field[2]-1) : i in [1..#a]];
	b := [Absolute_to_relative_dim(b[i], ground_field[2]-1) : i in [1..#b]];
	a1 := []; b1 := [];
	for i in [1..extension[2]-1] do
	    Append(~a1, [Relative_vector_to_NFelement1(a[i,j], ground_field, extension:KE:=K) : j in [1..ground_field[2]-1]]);
	    Append(~b1, [Relative_vector_to_NFelement1(b[i,j], ground_field, extension:KE:=K) : j in [1..ground_field[2]-1]]);
	end for;
	a := ElementToSequence((G!a1)*(G!b1));
	a := [ElementToSequence(a[i]) : i in [1..#a]];
	b := [];
	for i in [1..#a] do
	    for j in [1..ground_field[2]-1] do
		b cat:= Relative_NFelement_to_vector1(a[i,j], ground_field, extension);
	    end for;
	end for;
	return b;
    /* then the extension is multiquadratic */
    elif (ground_field[2] ne 2) and (extension[2] eq 2) then
	pol_ground := &+ [x^i : i in [0..ground_field[2]-1]];
	L<zeta_ground> := ext< K | pol_ground :Check:=false>;
	/* the galois closure of extension is itself */
	a := Absolute_to_relative_dim(f, ground_field[2]-1);
	b := Absolute_to_relative_dim(g, ground_field[2]-1);
	/* a := [Absolute_to_relative_dim(a[i], ground_field[2]-1) : i in [1..#a]]; */
	/* b := [Absolute_to_relative_dim(b[i], ground_field[2]-1) : i in [1..#b]]; */
	a1 := []; b1 := [];
	for i in [1..ground_field[2]-1] do
	    Append(~a1, Relative_vector_to_NFelement1(a[i], ground_field, extension:KE:=K));
	    Append(~b1, Relative_vector_to_NFelement1(b[i], ground_field, extension:KE:=K));
	end for;
	a := ElementToSequence((L!a1)*(L!b1));
	a := [ElementToSequence(a[i]) : i in [1..#a]];
	b := [];
	for i in [1..#a] do
	    b cat:= Relative_NFelement_to_vector1(a[i], ground_field, extension);
	end for;
	return b;
    /* finally ground is multiquadratic */
    elif (ground_field[2] eq 2) and (extension[2] ne 2) then
	/* the galois closure of ground is itself */
	pol_ext := &+ [x^i : i in [0..extension[2]-1]];
	L<zeta_ext> := ext< K | pol_ext :Check:=false>;
	a := Absolute_to_relative_dim(f, extension[2]-1);
	b := Absolute_to_relative_dim(g, extension[2]-1);
	/* a := [Absolute_to_relative_dim(a[i], ground_field[2]-1) : i in [1..#a]]; */
	/* b := [Absolute_to_relative_dim(b[i], ground_field[2]-1) : i in [1..#b]]; */
	a1 := []; b1 := [];
	for i in [1..extension[2]-1] do
	    Append(~a1, Relative_vector_to_NFelement1(a[i], ground_field, extension:KE:=K));
	    Append(~b1, Relative_vector_to_NFelement1(b[i], ground_field, extension:KE:=K));
	end for;
	a := ElementToSequence((L!a1)*(L!b1));
	a := [ElementToSequence(a[i]) : i in [1..#a]];
	b := [];
	for i in [1..#a] do
	    b cat:= Relative_NFelement_to_vector1(a[i], ground_field, extension);
	end for;
	return b;
    end if;
end function;


/* calculate product of f*F element of galois closure of K */
Galois_closure_multiplication_family := function(f, F, field_sequence, field_exponent)
    P<x> := PolynomialRing(Integers());
    K := KF_creation(field_sequence, field_exponent);
    pol := &+[ x^i : i in [0..field_exponent-1]];
    L<zeta> := ext< K | pol :Check:=false>;
    a := Vector_to_tower(f, field_exponent-1);
    a := [Vector_to_NFelement1(a[i], field_sequence, field_exponent:KF:=K) : i in [1..#a]];
    a := L!a;
    G := [];
    for i in [1..#F] do
	b := Vector_to_tower(F[i], field_exponent-1);
	b := [Vector_to_NFelement1(b[i], field_sequence, field_exponent:KF:=K) : i in [1..#b]];
	b := L!b;
	b := [NFelement_to_vector1(ElementToSequence(a*b)[i], field_sequence, field_exponent) : i in [1..field_exponent-1]];
	Append(~G, &cat b);
    end for;
    return G;
end function;


/* calculate product of f*F element of galois closure of K */
Relative_galois_closure_multiplication_family := function(f, F, ground_field, extension)
    G := [];
    for i in [1..#F] do
	Append(~G, Relative_galois_closure_multiplication(f, F[i], ground_field, extension));
    end for;
    return G;
end function;



/* minkowski action on basis and inverse minkowski action */
Minkowski_action := function(field_sequence, field_exponent)
    mink_action := []; inv_mink_action := [];
    field_dim := field_exponent^#field_sequence;
    F_p := GF(field_exponent);
    for i in [1..field_dim] do
	act := Galois_action_basis(IndexToExponent(i, #field_sequence, field_exponent), field_sequence, field_exponent);
	Append(~mink_action, act);
	act := ChangeRing((field_exponent-1)*ChangeRing(Vector(act), F_p), IntegerRing());
	Append(~inv_mink_action, ElementToSequence(act));
    end for;
    return mink_action, inv_mink_action;
end function;



KF_subfield_exponent := function(subfield_sequence, field_sequence, field_exponent: list_primes:=[])
    field_length := #field_sequence;
    subfield_length := #subfield_sequence;
    exp_vec := [ ZeroSequence(IntegerRing(), field_length) : i in [1..subfield_length]];
    /* V := RSpace(IntegerRing(field_exponent), field_length); */
    V := VectorSpace(GF(field_exponent), field_length);
    for beta in V do
	e := ElementToSequence(ChangeRing(beta, IntegerRing()));
	D := &* [field_sequence[i]^e[i] : i in [1..field_length]];
	for j in [1..subfield_length] do
	    if PrimeFreePart(D, field_exponent: list_primes:=list_primes) eq PrimeFreePart(subfield_sequence[j], field_exponent:list_primes:=list_primes) then
		exp_vec[j] := e;
	    end if;
	end for;
    end for;
    return exp_vec;
end function;


KF_subfield_index_basis := function(subfield_basis, field_basis, field_exponent)
    indexes := [];
    for i in [1..#subfield_basis] do
	Append(~indexes, Index(field_basis, subfield_basis[i]));
    end for;
    return indexes;
end function;


// embedding of L into K 
KF_embedding := function(x, subfield_basis, field_basis, field_exponent: subfield_index_basis := [])
    if #subfield_index_basis ne 0 then
	indexes := subfield_index_basis;
    else
	indexes := KF_subfield_index_basis(subfield_basis, field_basis, field_exponent);
    end if;
    y := ZeroSequence(RationalField(), #field_basis);
    for i in [1..#x] do
	y[indexes[i]] := x[i];
    end for;
    return y;
end function;


// embedding of L into K -- relative case
//CAREFUL -- ONLY KUMMER ARE SUPPORTED
Relative_embedding := function(x, ground_field, extension, upper_extension: subext_index_basis := [], extension_basis := [], upper_ext_basis := [])
    if #extension_basis eq 0 then
	ext_basis := KF_primefree_basis(extension[1], extension[2]);
    else
	ext_basis := extension_basis;
    end if;
    if #upper_ext_basis eq 0 then
	upp_ext_basis := KF_primefree_basis(upper_extension[1], upper_extension[2]);
    else
	upp_ext_basis := upper_ext_basis;
    end if;
    if #subext_index_basis ne 0 then
	indexes := subext_index_basis;
    else
	indexes := KF_subfield_index_basis(ext_basis, upp_ext_basis, extension[2]);
    end if;
    y := [];
    for i in [1..upper_extension[2]^#upper_extension[1]] do
	Append(~y, ZeroSequence(Rationals(), KF_dimension(ground_field)));
    end for;
    x1 := Vector_to_tower(x, extension[2]^#extension[1]);
    for i in [1..#x1] do
	y[indexes[i]] := x1[i];
    end for;
    return Tower_to_vector(y);
end function;


/* embedding of K into subfield  L  */
KF_subfield_embedding := function(x, subfield_basis, field_basis, field_exponent: subfield_index_basis := [])
    if #subfield_index_basis ne 0 then
	indexes := subfield_index_basis;
    else
	indexes := KF_subfield_index_basis(subfield_basis, field_basis, field_exponent);
    end if;
    y := ZeroSequence(RationalField(), #subfield_basis);
    for i in [1..#indexes] do
	y[i] := x[indexes[i]];
    end for;
    return y;
end function;


/* embedding of K into subfield  L  */
Relative_subfield_embedding := function(x, ground_field, subextension, extension: subext_index_basis := [], extension_basis := [], sub_ext_basis := [])
    if #extension_basis eq 0 then
	ext_basis := KF_primefree_basis(extension[1], extension[2]);
    else
	ext_basis := extension_basis;
    end if;
    if #sub_ext_basis eq 0 then
	sub_ext_basis := KF_primefree_basis(subextension[1], subextension[2]);
    else
	sub_ext_basis := sub_ext_basis;
    end if;
    if #subext_index_basis ne 0 then
	indexes := subext_index_basis;
    else
	indexes := KF_subfield_index_basis(sub_ext_basis, ext_basis, extension[2]);
    end if;
    y := [];
    for i in [1..subextension[2]^#subextension[1]] do
	Append(~y, ZeroSequence(Rationals(), KF_dimension(ground_field)));
    end for;
    dim := Relative_extension_dimension(ground_field, extension)[1];
    x1 := Absolute_to_relative_dim(x[1..dim], extension[2]^#extension[1]);
    for i in [1..#indexes] do
	y[i] := x1[indexes[i]];
    end for;
    return Tower_to_vector(y);
end function;


KF_embedding_family := function(U, subfield_basis, field_basis, field_exponent: subfield_index_basis := [])
    if #subfield_index_basis ne 0 then
	indexes := subfield_index_basis;
    else
	indexes := KF_subfield_index_basis(subfield_basis, field_basis, field_exponent);
    end if;
    family := [];
    for i in [1..#U] do
	y := ZeroSequence(RationalField(), #field_basis);
	for j in [1..#U[i]] do 
	    y[indexes[j]] := U[i,j];
	end for;
	Append(~family, y);
    end for;
    return family;
end function;


/* embedding of a family ok L/k in K/k (with L<K) -- relative version */
Relative_embedding_family := function(U, ground_field, extension, upper_extension)
    ext_basis := KF_primefree_basis(extension[1], extension[2]);
    upp_ext_basis := KF_primefree_basis(upper_extension[1], upper_extension[2]);
    indexes := KF_subfield_index_basis(ext_basis, upp_ext_basis, extension[2]);
    family := [];
    for i in [1..#U] do
	Append(~family, Relative_embedding(U[i], ground_field, extension, upper_extension:subext_index_basis := indexes, extension_basis := ext_basis, upper_ext_basis := upp_ext_basis));
    end for;
    return family;
end function;


KF_subfield_embedding_family := function(U, subfield_basis, field_basis, field_exponent: subfield_index_basis := [])
    if #subfield_index_basis ne 0 then
	indexes := subfield_index_basis;
    else
	indexes := KF_subfield_index_basis(subfield_basis, field_basis, field_exponent);
    end if;
    family := [ZeroSequence(RationalField(), #subfield_basis) : j in [1..#U]];
    for i in [1..#indexes] do
	for j in [1..#U] do 
	    family[j][i] := U[j][indexes[i]];
	end for;
    end for;
    return family;
end function;


/* embedding of a family ok K/k in L/k (with L<K) -- relative version */
Relative_subfield_embedding_family := function(U, ground_field, subextension, extension)
    ext_basis := KF_primefree_basis(extension[1], extension[2]);
    sub_ext_basis := KF_primefree_basis(subextension[1], subextension[2]);
    indexes := KF_subfield_index_basis(sub_ext_basis, ext_basis, extension[2]);
    family := [];
    for i in [1..#U] do
	Append(~family, Relative_subfield_embedding(U[i], ground_field, subextension, extension:subext_index_basis := indexes, extension_basis := ext_basis, sub_ext_basis := sub_ext_basis));
    end for;
    return family;
end function;


// Given a Galois morphism of K return its action on subfield L
MorphismRestriction := function(beta, subfield_sequence, field_sequence, field_exponent: list_primes:=[])
    b := ChangeRing(Vector(beta), GF(field_exponent));
    e := KF_subfield_exponent(subfield_sequence, field_sequence, field_exponent: list_primes:=list_primes);
    beta_subfield := [];
    for i in [1..#e] do
	alpha := e[i];
	a := ChangeRing(Vector(alpha), GF(field_exponent));
	t := InnerProduct(a, b);
	Append(~beta_subfield, IntegerRing() ! t);
    end for;
    return beta_subfield;
end function;


Relative_morphism_restriction := function(sigma, ground_field, extension, upper_extension)
    return [sigma[1], MorphismRestriction(sigma[2], extension[1], upper_extension[1], extension[2])];
end function;


/* Describe the action of the Minkowski embedding of K
     on element of L using morphisms of L
    the result is a sequence of indexes */
KF_minkowski_restriction := function(subfield_sequence, field_sequence, field_exponent: list_primes:=[])
    subfield_length := #subfield_sequence;
    field_length := #field_sequence;
    L := [];
    /* S := RSpace(IntegerRing(field_exponent), field_length); */
    S := VectorSpace(GF(field_exponent), field_length);
    for beta in S do
	b := ElementToSequence(ChangeRing(beta, IntegerRing()));
	beta_subfield := MorphismRestriction(b, subfield_sequence, field_sequence, field_exponent: list_primes:=list_primes);
	Append(~L, ExponentToIndex(beta_subfield, field_exponent));
    end for;
    return L;
end function;


/* Describe the action of the Minkowski embedding of K
     on element of L using morphisms of L
    the result is a sequence of indexes */
Relative_minkowski_restriction := function(ground_field, extension, upper_extension: list_primes:=[])
    V_ground := VectorSpace(GF(ground_field[2]), #ground_field[1]);
    V_upper_ext := VectorSpace(GF(upper_extension[2]), #upper_extension[1]);
    L := [];
    for sigma in V_upper_ext do
	for beta in V_ground do
	    s := ElementToSequence(ChangeRing(sigma, IntegerRing()));
	    b := ElementToSequence(ChangeRing(beta, IntegerRing()));
	    rest := Relative_morphism_restriction([b, s], ground_field, extension, upper_extension);
	    Append(~L, Relative_exponent_to_index(rest, ground_field, extension));
	end for;
    end for;
    return L;
end function;


/* Given the approximate logarithm over a field L
return the approximate logarithm over the field K */
ApproxLog_extension := function(Log_subfield, subfield_sequence, field_sequence, field_exponent:list_primes:=[])
    Log_field := ZeroSequence(RationalField(), field_exponent^(#field_sequence));
    RelMink := KF_minkowski_restriction(subfield_sequence, field_sequence, field_exponent:list_primes:=list_primes);
    for i in [1..#Log_field] do
	Log_field[i] := Log_subfield[RelMink[i]];
    end for;
    return Log_field;
end function;


/* Given the approximate logarithm over a field L
return the approximate logarithm over the field K */
Relative_ApproxLog_extension := function(Log, ground_field, extension, upper_extension:list_primes:=[])
    upp_ext_dim := Relative_extension_dimension(ground_field, upper_extension)[1];
    Log_field := ZeroSequence(RationalField(), upp_ext_dim);
    RelMink := Relative_minkowski_restriction(ground_field, extension, upper_extension);
    for i in [1..#Log_field] do
	Log_field[i] := Log[RelMink[i]];
    end for;
    return Log_field;
end function;


/* Given the approximate logarithm over a field L
return the approximate logarithm over the field K */
ApproxLog_extension_family := function(Log_subfield_family, subfield_sequence, field_sequence, field_exponent:list_primes:=[])
    field_dim := field_exponent^(#field_sequence);
    Log_field_family := [ZeroSequence(RationalField(), field_dim) : i in [1..#Log_subfield_family]];
    RelMink := KF_minkowski_restriction(subfield_sequence, field_sequence, field_exponent:list_primes:=list_primes);
    for i in [1..field_dim] do
	for j in [1..#Log_subfield_family] do
	    Log_field_family[j, i] := Log_subfield_family[j, RelMink[i]];
	end for;
    end for;
    return Log_field_family;
end function;


/* Given the approximate logarithm over a field L
return the approximate logarithm over the field K */
Relative_ApproxLog_extension_family := function(Log_family, ground_field, extension, upper_extension)
    upp_ext_dim := Relative_extension_dimension(ground_field, upper_extension)[1];
    Log_field_family := [ZeroSequence(RationalField(), upp_ext_dim) : i in [1..#Log_family]];
    RelMink := Relative_minkowski_restriction(ground_field, extension, upper_extension);
    for i in [1..upp_ext_dim] do
	for j in [1..#Log_field_family] do
	    Log_field_family[j, i] := Log_family[j, RelMink[i]];
	end for;
    end for;
    return Log_field_family;
end function;


Complete_extension := function(U, subfield_sequence, subfield_basis, field_sequence, field_basis, field_exponent: list_primes:=[], subfield_index_basis := [])
    U1 := [U[i,1] : i in [1..#U]];
    U2 := [U[i,2] : i in [1..#U]];
    U1 := KF_embedding_family(U1, subfield_basis, field_basis, field_exponent: subfield_index_basis := subfield_index_basis);
    U2 := ApproxLog_extension_family(U2, subfield_sequence, field_sequence, field_exponent:list_primes:=list_primes);
    return [[U1[i], U2[i]] : i in [1..#U1]];
end function;


Relative_complete_extension := function(U, ground_field, extension, upper_extension)
    U1 := [U[i,1] : i in [1..#U]];
    U2 := [U[i,2] : i in [1..#U]];
    U1 := Relative_embedding_family(U1, ground_field, extension, upper_extension);
    U2 := Relative_ApproxLog_extension_family(U2, ground_field, extension, upper_extension);
    return [[U1[i], U2[i]] : i in [1..#U1]];
end function;


/* permutation of morphisms induced by morphism beta */
/* return indices */
Induced_permutation := function(beta, field_exponent)
    n := #beta;
    ZZ := IntegerRing();
    S := VectorSpace(GF(field_exponent), n);
    u := S ! beta;
    P := [];
    for v in S do
	x := ElementToSequence(ChangeRing(u + v, ZZ));
	Append(~P, ExponentToIndex(x, field_exponent));
    end for;
    return P;
end function;


/* permutation of morphisms induced by morphism sigma */
/* return indices */
Relative_induced_permutation := function(sigma, ground_field, extension)
    n_ground := #sigma[1];
    n_ext := #sigma[2];
    ZZ := IntegerRing();
    V_ground := VectorSpace(GF(ground_field[2]), n_ground);
    V_ext := VectorSpace(GF(extension[2]), n_ext);
    u_ground := V_ground ! sigma[1];
    u_ext := V_ext ! sigma[2];
    P := [];
    for v in V_ground do
	x_ground := ElementToSequence(ChangeRing(u_ground + v, ZZ));
	for w in V_ext do
	    x_ext := ElementToSequence(ChangeRing(u_ext + w, ZZ));
	    Append(~P, Relative_exponent_to_index([x_ground, x_ext], ground_field, extension));
	end for;
    end for;
    return P;
end function;


Induced_log_permutation := function(L, beta, field_exponent)
    L_perm := [];
    perm := Induced_permutation(beta, field_exponent);
    for i in [1..#L] do
	Append(~L_perm, L[perm[i]]);
    end for;
    return L_perm;
end function;


Relative_log_permutation := function(Log, sigma, ground_field, extension)
    L_perm := [];
    perm := Relative_induced_permutation(sigma, ground_field, extension);
    for i in [1..#Log] do
	Append(~L_perm, Log[perm[i]]);
    end for;
    return L_perm;
end function;


/* // return sequence of exponent defining elements of dL as products of elements of dK */
/* // For now dK is supposed to be a sequence of prime numbers */
/* Subfield_exponent := function(dL, dK) */
/* m := #dL; n := #dK; e := []; */
/* for k in [1..m] do */
/*     ek := []; */
/*     for l in [1..n] do */
/* 	Append(~ek, MC_Valuation(dL[k], dK[l])); */
/*     end for; */
/*     Append(~e, ek); */
/* end for; */
/* return e; */
/* end function; */


/* Subfield_Index_full := function(dL, d) */
/* E := Subfield_exponent_full(dL, d); */
/* I := []; */
/* for i in [1..#E] do */
/*     Append(~I, ExponentToIndex(E[i]));  */
/* end for; */
/* return I; */
/* end function; */


/* /\* Given an element of L, return its embedding in K  */
/* L and K are supposed to be given by defining sequences  */
/* Subfield_embedding := function(x, dL, dK) */
/* n := #dK; m := #dL; */
/* e := Subfield_exponent(dL, dK); */
/* z := ZeroSequence(RationalField(), 3^n); */
/* end function; *\/ */
/* // Same as before */
/* Subfield_embedding1 := function(x, dL, dK) */
/* L := MCF_creation(dL:Check:=false); K := MCF_creation(dK:Check:=false); IsSubfield(L, K); */
/* return NFelement_to_vector1((K ! Vector_to_NFelement1(x, L)), dK); */
/* end function; */



/* /\* Given a morphism of L return the induced permutation */
/* on the approx-log over K *\/ */
/* RelativeLog_permutation := function(u, LogK, dL, dK) */
/* n := #dK; m := #dL; */
/* RelMink := RelativeMinkowskiAction(dL, dK); */
/* LogL := ZeroSequence(RationalField(), 3^m); */
/* for i in [1..3^m] do */
/*     I := Index(RelMink, i); */
/*     LogL[i] := LogK[I]; */
/* end for; */
/* P := InducedPermutation(u); */
/* NewRelMink := [P[RelMink[i]] : i in [1..3^(n)]]; */
/* return [LogL[NewRelMink[i]] : i in [1..#LogK]]; */
/* end function; */



/* relative norm with respect of morphism sigma which is  */
KF_norm_morphism_simple := function(f, beta, field_sequence, field_exponent)
    g := f;
    for i in [1..field_exponent-1] do
	g := Galois_closure_mult_scalar(f, Galois_morphism_closure(g, beta, field_sequence, field_exponent), field_sequence, field_exponent);
    end for;
    return g;
end function;



/* relative norm with respect of morphism sigma which is of the form [0,sigma2]  */
Relative_norm_morphism_simple := function(f, sigma, ground_field, extension)
    g := f;
    for i in [1..extension[2]-1] do
	g := Relative_galois_closure_mult_scalar_family(f, [Relative_galois_morphism_closure(g, sigma, ground_field, extension)], ground_field, extension)[1];
    end for;
    return g;
end function;



/* ######################################################### */
/* ##################   ideal related ###############  */
/* ######################################################### */


//create HNF of ideal generated by g
KF_IntegralBasis_creation := function(g, field_sequence, field_exponent: Det:=1)
    Z := ZeroSequence(RationalField(), field_exponent^#field_sequence);
    B := [];
    K := KF_creation(field_sequence, field_exponent:Check:=false);
    for i in [1..field_exponent^#field_sequence] do
	v := Z;
	v[i] := 1;
	Append(~B, NFelement_to_vector1(Vector_to_NFelement1(g, field_sequence, field_exponent:KF:=K)*Vector_to_NFelement1(v, field_sequence, field_exponent:KF:= K), field_sequence, field_exponent));
    end for;
    B := Matrix(B);
    dB := Denominator(B);
    B := B*dB;
    B := ChangeRing(B, IntegerRing());
    /* print Rank(B); */
    /* print "before hermite form"; */

    if (Det eq 1) then
	B := HermiteForm(ChangeRing(B, IntegerRing()));
    else
	H := Det*IdentityMatrix(IntegerRing(), Ncols(B));
        B := ChangeRing(HNF_update_classical(H, B), Integers());
    end if;
    /* print "after hermite form"; */
    B := ChangeRing(B, RationalField())/dB;
    B := [ElementToSequence(B[i]) : i in [1..Rank(B)]];
    return B;
end function;


//create HNF of ideal generated by g
Relative_IntegralBasis_creation := function(g, ground_field, extension)
    field_dim := Relative_extension_dimension(ground_field, extension)[1];    
    Z := ZeroSequence(RationalField(), field_dim);
    B := [];
    K := Relative_extension_creation(ground_field, extension);
    for i in [1..field_dim] do
	v := Z;
	v[i] := 1;
	Append(~B, Relative_NFelement_to_vector1(Relative_vector_to_NFelement1(g, ground_field, extension:KE:=K)*Relative_vector_to_NFelement1(v, ground_field, extension:KE:= K), ground_field, extension));
    end for;
    B := Matrix(B);
    dB := Denominator(B);
    B := B*dB;
    B := HermiteForm(ChangeRing(B, IntegerRing()));
    B := ChangeRing(B, RationalField())/dB;
    B := [ElementToSequence(B[i]) : i in [1..Rank(B)]];
    return B;
end function;


/* two element representation -- probalistic version */
Kummer_Ideal_two_elements := function(I, kf)
    M := Matrix(I);
    d := Determinant(M);
    M := LLL(M);
    a := RandomElement_lattice(M: size:=1);
    /* a := ZeroSequence(Rationals(),Ncols(M)); */
    /* a[1] := 1; */
    A := KF_IntegralBasis_creation(a, kf[1], kf[2]);
    dH := 1;
    i:=0;
    while dH ne d do
	i+:=1;
	/* print i; */
	H := Matrix(A);
	b := RandomElement_lattice(M: size:=2);
	B := Matrix(KF_IntegralBasis_creation(b, kf[1], kf[2]));
	H := ChangeRing(HNF_update_classical(H, B), Integers());
	dH := Determinant(H);
    end while;
    return [a, b];
end function;


KF_ideal_product := function(J, I, kf)
    L := KF_creation(kf[1], kf[2]);
    I := [Vector_to_NFelement1(I[j], kf[1], kf[2]: KF:=L) : j in [1..#I]];
    if #J gt 2 then
	H := Kummer_Ideal_two_elements(J, kf);
    else
	H := J;
    end if;
    I1 := [NFelement_to_vector1(Vector_to_NFelement1(H[1], kf[1], kf[2]: KF:=L)*I[j], kf[1], kf[2]) : j in [1..#I]];
    I2 := [NFelement_to_vector1(Vector_to_NFelement1(H[2], kf[1], kf[2]: KF:=L)*I[j], kf[1], kf[2]) : j in [1..#I]];
    H := HermiteForm(ChangeRing(Matrix(I1), Integers()));
    H := HNF_update_classical(H, ChangeRing(Matrix(I2), Integers()));
    H := [Eltseq(H[i]) : i in [1..Nrows(H)]];
    return H;
end function;


KF_ideal_power := function(J, exp, kf)
    L := KF_creation(kf[1], kf[2]);
    I := J;
    if #J gt 2 then
	H := Kummer_Ideal_two_elements(J, kf);
    else
	H := J;
    end if;
    for i in [1..exp-1] do
	I := [Vector_to_NFelement1(I[j], kf[1], kf[2]: KF:=L) : j in [1..#I]];    
	I1 := [NFelement_to_vector1(Vector_to_NFelement1(H[1], kf[1], kf[2]: KF:=L)*I[j], kf[1], kf[2]) : j in [1..#I]];
	I2 := [NFelement_to_vector1(Vector_to_NFelement1(H[2], kf[1], kf[2]: KF:=L)*I[j], kf[1], kf[2]) : j in [1..#I]];
	I := HermiteForm(ChangeRing(Matrix(I1), Integers()));
	I := HNF_update_classical(I, ChangeRing(Matrix(I2), Integers()));
	I := [Eltseq(I[i]) : i in [1..Nrows(I)]];
    end for;
    return I;
end function;



/* two element representation -- probalistic version */
Kummer_relative_norm_prob := function(I, kf, kf_sub, sigma)
    field_basis := KF_primefree_basis(kf[1], kf[2]);
    subfield_basis := KF_primefree_basis(kf_sub[1], kf_sub[2]);
    M := ChangeRing(Matrix(I), Integers());
    /* time M := LLL(ChangeRing(Matrix(I), Integers())); */
    /* print "after LLL"; */
    d := Determinant(M);
    sub_dim := KF_dimension(kf_sub);
    /* L := []; */
    /* for i in [1..Nrows(M)] do */
    /* a := KF_norm_morphism_simple(Eltseq(M[i]), sigma, kf[1], kf[2]); */
    /* a := KF_subfield_embedding(a, subfield_basis, field_basis, kf[2]); */
    /* Append(~L, a); */
    /* end for; */
    /* L := Matrix(L); */
    /* L := LLL(L); */
    /* L := RowSubmatrixRange(L, 1, Rank(L)); */
    /* L := ChangeRing(L, Integers()); */
    /* L := Denominator(L)*L; */
    /* L := HermiteForm(L); */
    a := RandomElement_lattice(M: size:=1);
    a := KF_norm_morphism_simple(a, sigma, kf[1], kf[2]);
    a := KF_subfield_embedding(a, subfield_basis, field_basis, kf[2]);
    /* print "before computing hnf first element"; */
    a := [Integers()!a[i] mod d : i in [1..#a]];
    A := KF_IntegralBasis_creation(a, kf_sub[1], kf_sub[2]: Det:=d);
    /* print "after computing hnf first element"; */
    i := 0;
    H := Matrix(A);
    dH := Determinant(H);
    while AbsoluteValue(dH/d) ne 1 do
	i+:=1;
	/* print i; */
	/* print dH, d; */
	/* print Factorisation(Integers()!(dH/d)); */
	/* readi jbjhb; */
	/* H := Matrix(A); */
	b := RandomElement_lattice(M: size:=1);
	b := KF_norm_morphism_simple(Eltseq(b), sigma, kf[1], kf[2]);
	/* print b; */
	b := KF_subfield_embedding(b, subfield_basis, field_basis, kf[2]);
	/* print b; */
	b := ChangeUniverse(b, Integers());
	b := [b[i] mod d : i in [1..#b]];
	B := Matrix(KF_IntegralBasis_creation(b, kf_sub[1], kf_sub[2]: Det:=d));
	H := ChangeRing(HNF_update_classical(H, B), Integers());
	dH := Determinant(H);
    end while;
    
    return H;
end function;

/* two element representation -- probalistic version */
Kummer_relative_norm_prob_two := function(I, kf, kf_sub, sigma)
    field_basis := KF_primefree_basis(kf[1], kf[2]);
    subfield_basis := KF_primefree_basis(kf_sub[1], kf_sub[2]);
    time M := LLL(ChangeRing(Matrix(I), Integers()));
    print "after lll";
    d := Determinant(M);
    sub_dim := KF_dimension(kf_sub);
    L := [];
    /* for i in [1..Nrows(M)] do */
    /* a := KF_norm_morphism_simple(Eltseq(M[i]), sigma, kf[1], kf[2]); */
    /* a := KF_subfield_embedding(a, subfield_basis, field_basis, kf[2]); */
    /* Append(~L, a); */
    /* end for; */
    /* L := Matrix(L); */
    /* L := LLL(L); */
    a := KF_norm_morphism_simple(Eltseq(M[1]), sigma, kf[1], kf[2]);
    a := KF_subfield_embedding(a, subfield_basis, field_basis, kf[2]);
    A := KF_IntegralBasis_creation(a, kf_sub[1], kf_sub[2]);
    dH := 1;
    i:=0;
    H := Matrix(A);
    while AbsoluteValue(dH/d) ne 1 do
	/* i+:=1; */
	/* print i; */
	H := Matrix(A);
	b := RandomElement_lattice(M: size:=1);
	b := KF_norm_morphism_simple(Eltseq(b), sigma, kf[1], kf[2]);
	/* print b; */
	b := KF_subfield_embedding(b, subfield_basis, field_basis, kf[2]);
	/* print b; */
	b := ChangeUniverse(b, Integers());
	B := Matrix(KF_IntegralBasis_creation(b, kf_sub[1], kf_sub[2]));
	H := ChangeRing(HNF_update_classical(H, B), Integers());
	dH := Determinant(H);
	/* print dH, d; */
	/* print Factorisation(Integers()!(dH/d)); */
    end while;
    return H;

    /* H := ChangeRing(Matrix(Vector(a)), Integers()); */
    /* for i in [2..#I] do */
    /*     print i; */
    /*     a := ChangeUniverse(KF_norm_morphism_simple(Eltseq(M[i]), sigma, kf[1], kf[2])[1..sub_dim], Integers()); */
    /*     H := HNF_addvector_classical(H, a); */
    /* end for; */
    /* print d/Determinant(H); */
    /* R := Rank(H); */
    /* print R; */
    /* print H; */
    /* readi hjghv; */
    /* while R lt sub_dim do */
    /*     a := RandomElement_lattice(M); */
    /*     a := KF_norm_morphism_simple(a, sigma, kf[1], kf[2])[1..sub_dim]; */
    /*     a := ChangeUniverse(a, Integers()); */
    /*     H := HNF_addvector_classical(H, a); */
    /*     R := Rank(H); */
    /* end while; */
    /* i:=0; */
    /* dH := Determinant(H); */
    /* bool := false; */
    /* /\* return H; *\/ */
    /* while not (bool) do */
    /*     i+:=1; */
    /*     print i; */
    /*     a := RandomElement_lattice(M: size:=1); */
    /*     print a; */
    /*     a := KF_norm_morphism_simple(a, sigma, kf[1], kf[2])[1..sub_dim]; */
    /*     a := ChangeUniverse(a, Integers()); */
    /*     H := HNF_addvector_classical(H, a); */
    /*     dH := Determinant(H); */
    /*     print Factorisation(Integers()!(dH/d)); */
    /*     bool := AbsoluteValue(d/dH) eq 1; */
    /* end while; */
    /* return H; */
end function;


KF_subfield_lattice := function(subfield_sequence, field_sequence, field_exponent:galois_closure := true, denominator:=1)
    NK := field_exponent^(#field_sequence);
    NF := field_exponent^(#subfield_sequence);
    field_basis := KF_primefree_basis(field_sequence, field_exponent);
    subfield_basis := KF_primefree_basis(subfield_sequence, field_exponent);
    indexes := KF_subfield_index_basis(subfield_basis, field_basis, field_exponent);
    l := ZeroSequence(RationalField(), NF);
    L := [];
    for i in [1..NF] do
	l[i] := 1;
	Append(~L, KF_embedding(l, subfield_basis, field_basis, field_exponent:subfield_index_basis:= indexes));
	l[i] := 0;
    end for;
    if galois_closure then
	return LatticeWithBasis(HorizontalJoin(Matrix(IntegerRing(), L), ZeroMatrix(IntegerRing(), NF, (field_exponent-2)*NK))), subfield_basis, field_basis;
    else
	return LatticeWithBasis(Matrix(IntegerRing(), L)), subfield_basis, field_basis;
    end if;
end function;


Relative_subfield_lattice := function(ground_field, subextension, extension:galois_closure := true, denominator:=1)
    subextension_dim := Relative_extension_dimension(ground_field, subextension)[1];
    extension_dim := Relative_extension_dimension(ground_field, extension)[1];
    l := ZeroSequence(RationalField(), subextension_dim);
    L := [];
    for i in [1..subextension_dim] do
	l[i] := 1;
	Append(~L, Relative_embedding(l, ground_field, subextension, extension));
	l[i] := 0;
    end for;
    if galois_closure then
	return LatticeWithBasis(HorizontalJoin(Matrix(IntegerRing(), L), ZeroMatrix(IntegerRing(), subextension_dim, ((ground_field[2]-1)*(extension[2]-1)-1)*extension_dim)));
    else
	return LatticeWithBasis(Matrix(IntegerRing(), L));
    end if;
end function;


Subfield_lattice_intersection := function(L, subfield_sequence, field_sequence, field_exponent:galois_closure:=true, denominator:=1)
    LF, subfield_basis, field_basis := KF_subfield_lattice(subfield_sequence, field_sequence, field_exponent:galois_closure:=galois_closure, denominator:=denominator);
    test_basis := Lattice_intersection(ChangeRing(Matrix(L), Integers()), BasisMatrix(LF));
    test_basis := [ElementToSequence(ChangeRing(test_basis[i], Rationals())) : i in [1..Nrows(test_basis)]];
    test_basis := KF_subfield_embedding_family(test_basis, subfield_basis, field_basis, field_exponent);
    return test_basis;
end function;


Relative_subfield_lattice_intersection := function(L, ground_field, subextension, extension: galois_closure:=true, denominator:=1)
    LF := Relative_subfield_lattice(ground_field, subextension, extension: galois_closure:=galois_closure, denominator:=denominator);
    test_basis := Lattice_intersection(ChangeRing(Matrix(L), Integers()), BasisMatrix(LF));
    /* test_basis := BasisMatrix(Lattice(ChangeRing(Matrix(L), Integers())) meet Lattice(BasisMatrix(LF))); */
    test_basis := [ElementToSequence(ChangeRing(test_basis[i], Rationals())) : i in [1..Nrows(test_basis)]];
    test_basis := Relative_subfield_embedding_family(test_basis, ground_field, subextension, extension);
    return test_basis;
end function;


KF_norm_equation_simple := function(norm, field_sequence, field_exponent)
    same_norm_list := [* [* *], [* *] *];
    field_length := #field_sequence;
    exponents := [];
    V := VectorSpace(GF(field_exponent), field_length);
    S := Set(V);
    while #S gt 0 do
	#S;
	alpha := Random(S);
	W := sub<V | alpha>;
	T := Exclude(Set(W), W!ZeroSequence(Integers(), field_length));
	L := [PrimeFreePart(&*[field_sequence[i]^(Integers()!w[i]) : i in [1..field_length]], field_exponent) : w in T]; 
	subfield_sequence := [Min(L)];
	subfield_sequence;
	s := false;
	while s eq false do
	    time K := KF_creation(subfield_sequence, field_exponent);
	    time U := UnitGroup(K);
	    time CL := ClassGroup(K);
	    time t, x := NormEquation(K, Integers()!norm);
	    x;
	    if #same_norm_list[1] eq 0 then
		s := x[1] in MaximalOrder(K);
	    else
		j := Random(1, #same_norm_list[1]);
		E := KF_creation(subfield_sequence cat same_norm_list[1,j], field_exponent);
		K2 := KF_creation(same_norm_list[1,j], field_exponent);
		b, m := IsSubfield(K, E);
		b2, m2 := IsSubfield(K2, E);
		x2 := E!Vector_to_NFelement1(same_norm_list[2,j], same_norm_list[1,j], field_exponent:KF:=K2);
		y := NFelement_to_vector1(x2/(E!x[1]), subfield_sequence cat same_norm_list[1,j], field_exponent);
		d := Integers()!Denominator(Vector(y));
		fact := Factorisation(d);
		s := (x[1] in MaximalOrder(K)) and ((d eq 1) or ((#fact eq 1) and (fact[1,1] eq field_exponent)));
	    end if;
	end while;
	x := NFelement_to_vector1(x[1], subfield_sequence, field_exponent);
	Append(~same_norm_list[1], subfield_sequence);
	Append(~same_norm_list[2], x);
	S := S diff Set(sub<V | alpha>);
    end while;
    return same_norm_list;
end function;



Subfield_from_vector := function(x, field_sequence, field_exponent)
    V := VectorSpace(GF(field_exponent), #field_sequence);
    Mink := Minkowski_embedding(x, field_sequence, field_exponent);
    Indexes := [];
    for i in [2..#Mink] do
	if Mink[1] eq Mink[i] then
	    Append(~Indexes, i);
	end if;
    end for;
    Exponents := [ChangeUniverse(IndexToExponent(Indexes[i], #field_sequence, field_exponent), GF(field_exponent)) : i in [1..#Indexes]];
    if #Exponents eq 0 then
	return field_sequence;
    else
	M := (Matrix(Exponents));
	K := ChangeRing(KernelMatrix(Transpose(M)), IntegerRing());
	subfield_sequence := [];
	for j in [1..Nrows(K)] do
	    Append(~subfield_sequence, &* [field_sequence[i]^K[j, i] : i in [1..#field_sequence]] );
	end for;
	return subfield_sequence;
    end if;
end function;



KF_discriminant_pf := function(kummer_field)
    dim := KF_dimension(kummer_field);
    d := &*kummer_field[1]^((dim div kummer_field[2]) * (kummer_field[2]-1));
    d *:= kummer_field[2]^(dim*#kummer_field[1]);
    return d;
end function;
