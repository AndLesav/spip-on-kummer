/* index to exponent */
IndexToExponent := function(I, n, p)
    J := I - 1; e := [];
    for i in [0..n-1] do
	Append(~e, J div p^(n-1-i));
	J := J mod p^(n-1-i);
    end for;
    return Reverse(e);
end function;

// "exponent" to index
ExponentToIndex := function(e, p)
    n := #e;
    I := 1 + (&+ [e[i]*p^(i-1) : i in [1..n]]);
    return I;
end function;

List_indexes_conjugates := function(n, p)
    V := VectorSpace(GF(p), n);
    list_indexes_pair := [];
    placed_indexes := [];
    for v in V do
	if v ne V!0 then
	    gamma := Eltseq(ChangeRing(v, Integers()));
	    gamma_conj := Eltseq(ChangeRing(-v, Integers()));
	    i_gamma := ExponentToIndex(gamma, p);
	    i_gamma_conj := ExponentToIndex(gamma_conj, p);
	    ind := Index(placed_indexes, i_gamma);
	    if ind eq 0 then
		Append(~list_indexes_pair, [i_gamma, i_gamma_conj]);
		Append(~placed_indexes, i_gamma);
		Append(~placed_indexes, i_gamma_conj);
	    end if;
	end if;
    end for;
    return list_indexes_pair;
end function;


// dimension of kummer field
KF_dimension := function(field)
    return field[2]^#field[1];
end function;

KF_is_simple := function(field)
    if #field[1] eq 1 then
	return true;
    else
	return false;
    end if;
end function;


Absolute_to_relative_index := function(I, ground_field, extension)
    I_ext := 1 + ( (I-1) div ground_field[2]^#ground_field[1]);
    I_ground := ((I-1) mod ground_field[2]^#ground_field[1]) +1 ;
    return [I_ext, I_ground];
end function;

Relative_to_absolute_index := function(I, ground_field, extension)
    ground_dim := KF_dimension(ground_field);
    return (I[1]-1)*ground_dim+I[2];
end function;

Relative_index_to_exponent := function(I, ground_field, extension)
    e_ext := IndexToExponent(I[1], #extension[1], extension[2]);
    e_ground := IndexToExponent(I[2], #ground_field[1], ground_field[2]);
    return [e_ground, e_ext];
end function;

Absolute_index_to_exponent := function(I, ground_field, extension)
    return Relative_index_to_exponent(Absolute_to_relative_index(I, ground_field, extension), ground_field, extension);
end function;

Relative_exponent_to_index := function(exponent, ground_field, extension)
    index_ground := ExponentToIndex(exponent[1], ground_field[2]);
    index_ext := ExponentToIndex(exponent[2], extension[2]);
    ground_dim := KF_dimension(ground_field);
    return (index_ext-1)*ground_dim + index_ground;
end function;

Relative_extension_dimension := function(ground_field, extension)
    a := KF_dimension(ground_field);
    b := KF_dimension(extension);
    return [a*b, b, a];
end function;


KF_signature := function(kummer_field)
    if kummer_field[2] eq 2 then
	r1 := KF_dimension(kummer_field);
	r2 := 0;
    else
	r1 := 1;
	r2 := (KF_dimension(kummer_field)-1) div 2;
    end if;
    return r1, r2;
end function;

Relative_extension_signature := function(ground_field, extension)
    g1, g2 := KF_signature(ground_field);
    e1, e2 := KF_signature(extension);
    r1 := g1*e1;
    r2 := (Relative_extension_dimension(ground_field, extension)[1]-r1) div 2;
    return r1, r2;
end function;

// Field creation given a sequence d
// d is supposed to be "reduced'
KF_creation := function(field_sequence, field_exponent: Check:=false)
    p<x> := PolynomialRing(RationalField());
    n := #field_sequence;
    K := NumberField([x^field_exponent - field_sequence[n+1-i] : i in [1..n]]:Check:=Check);
    return K;
end function;


/* field creation as relative extension
need a ground field and the extension 
fields are defined by a sequence of elements and exponent for kummer extension or a polynomial 
CAREFUL : ONLY KUMMER ARE SUPPORTED
*/
Relative_extension_creation := function(ground_field, extension: Check:=false)
    p<x> := PolynomialRing(Integers());
    F := KF_creation(ground_field[1], ground_field[2]);
    n := #extension[1];
    if n eq 0 then return F; end if;
    K := ext<F | [x^extension[2] - extension[1][n+1-i] : i in [1..n]]:Check:=Check>;
    return K, F; 
end function;

/* naive QQ-basis for a kummer field */
KF_naive_basis := function(field_sequence, field_exponent)
    if #field_sequence eq 0 then
	return [];
    else
	basis_sequence := [];
	field_length := #field_sequence;
	field_dim := field_exponent^field_length;
	for i in [1..field_dim] do
	    e := IndexToExponent(i, field_length, field_exponent);
	    Append(~basis_sequence, &*[field_sequence[j]^e[j] : j in [1..field_length]]);
	end for;
	return basis_sequence;
    end if;
end function;

/* naive basis of ground field and extension */
//CAREFUL : ONLY KUMMER ARE SUPPORTED
Relative_naive_basis := function(ground_field, extension)
    ground_basis := KF_naive_basis(ground_field[1], ground_field[2]);
    extension_basis := KF_naive_basis(extension[1], extension[2]);
    return extension_basis, ground_basis;
end function;

/* prime-power free QQ basis */
KF_primefree_basis := function(field_sequence, field_exponent:list_primes := [])
    basis := KF_naive_basis(field_sequence, field_exponent);
    return PrimeFreeSequence(basis, field_exponent : list_primes := list_primes);
end function;  


KF_diff_basis := function(kummer, depth)
    length := #kummer[1];
    sub := <kummer[1][1..length-depth], kummer[2]>;
    ext := <kummer[1][length-depth+1..length], kummer[2]>;
    b_k := KF_primefree_basis(kummer[1], kummer[2]);
    b_s := KF_primefree_basis(sub[1], sub[2]);
    b_e := KF_primefree_basis(ext[1], ext[2]);
    b_se := Eltseq(TensorProduct(Vector(b_e), Vector(b_s)));
    return [Integers()!Root(b_se[i]/b_k[i], kummer[2]) : i in [1..#b_k]], b_e;
end function;


/* prime-power free basis of ground field and extension */
//CAREFUL : ONLY KUMMER ARE SUPPORTED
Relative_primefree_basis := function(ground_field, extension)
    ground_basis_r, ground_basis_q := KF_primefree_basis(ground_field[1], ground_field[2]);
    extension_basis_r, extension_basis_q := KF_primefree_basis(extension[1], extension[2]);
    return [extension_basis_r, extension_basis_q], [ground_basis_r, ground_basis_q];
end function;


/* goes to tower representation to absolute  */
Tower_to_vector := function(f)
    if (Type(f[1]) eq RngIntElt) or (Type(f[1]) eq FldRatElt) then
	return f;
    else
	return &cat [$$(f[i]) : i in [1..#f]];
    end if;
end function;


/* absolute field to tower */
Vector_to_tower := function(f, p)
    if p eq 1 then
	return [f];
    end if;
    N := #f;
    length := N div p;
    test := N mod p;
    if test ne 0 then
	return f;
    else
	return [$$(f[(i-1)*length+1..i*length], p) : i in [1..p]];
    end if;
end function;


/* absolute to tower, changing from powerfree basis to naive basis */
Vector_to_tower1 := function(f, field_sequence, field_exponent: basis_q := [], list_primes := [])
    N := #f;
    f := ChangeUniverse(f, Rationals());
    if #basis_q eq 0 then
	basis_r, basis := KF_primefree_basis(field_sequence, field_exponent: list_primes:=list_primes);
    else
	basis := basis_q;
    end if;
    // f := ChangeUniverse(f, RationalField());
    g := [];
    for i in [1..N] do
	Append(~g, f[i]/basis[i]);
    end for;
    return Vector_to_tower(g, field_exponent);
end function;


/* absolute to tower, changing from powerfree basis to naive basis */
//CAREFUL : ONLY KUMMER ARE SUPPORTED
Relative_vector_to_tower1 := function(f, ground_field, extension: basis_q := [], list_primes := [])
    g := ChangeUniverse(f, Rationals());
    if #extension[1] eq 0 then
	return Vector_to_tower1(g, ground_field[1], ground_field[2]);
    else
	g := Vector_to_tower(f, extension[2]^#extension[1]);
	basis_ext, basis_ground := Relative_primefree_basis(ground_field, extension);
	h := [];
	for i in [1..#g] do
	    for j in [1..#g[i]] do
		g[i, j] := g[i, j]/(basis_ground[2,j]*basis_ext[2,i]);
	    end for;
	    Append(~h, Vector_to_tower(g[i], ground_field[2]));
	end for;
	h := &cat h;
	return Vector_to_tower(h, extension[2]);
    end if;
end function;


/* vector to NF, going fron powerfree basis to naive basis */
Vector_to_NFelement1 := function(f, field_sequence, field_exponent: KF:= RationalField())
    if #f ne field_exponent^#field_sequence then "ELEMENT DOES NOT HAVE RIGHT LENGTH"; return false; end if;
    g := Vector_to_tower1(f, field_sequence, field_exponent);
    if KF ne RationalField() then
	return (KF!g);
    else
	K := KF_creation(field_sequence, field_exponent);
	return (K ! g);
    end if;
end function;


/* vector to NF, going fron powerfree basis to naive basis -- relative version 
CAREFUL : ONLY KUMMER ARE SUPPORTED*/
Relative_vector_to_NFelement1 := function(f, ground_field, extension: KE:= RationalField())
    if #f ne (ground_field[2]^#ground_field[1])*extension[2]^#extension[1] then "ELEMENT DOES NOT HAVE RIGHT LENGTH"; return false; end if;
    g := Relative_vector_to_tower1(f, ground_field, extension);
    if KE ne RationalField() then
	return (KE!g);
    else
	K := Relative_extension_creation(ground_field, extension);
	return (K ! g);
    end if;
end function;


/* NF to vector in naive basis */
NFelement_to_vector := function(f, field_sequence, field_exponent)
    field_length := #field_sequence;
    seq := field_sequence;
    if field_length eq 0 then
	return [f];
    else
	g := ElementToSequence(f);
	Prune(~seq);
	return &cat [$$(g[i], seq, field_exponent) : i in [1..#g]];
    end if;
    g := ElementToSequence(f);
end function;


/* NF to vector, from naive to powerfree basis */
NFelement_to_vector1 := function(f, field_sequence, field_exponent: basis_q := [], list_primes := [])
    if #basis_q eq 0 then
	basis_r, basis := KF_primefree_basis(field_sequence, field_exponent: list_primes:=list_primes);
    else
	basis := basis_q;
    end if;
    g := NFelement_to_vector(f, field_sequence, field_exponent);
    for i in [1..#g] do
	g[i] := g[i]*basis[i];
    end for;
    return g;
end function;


/* relative NF to vector, from naive to powerfree basis  */
// CAREFUL : ONLY KUMMER ARE SUPPORTED
Relative_NFelement_to_vector1 := function(f, ground_field, extension)
    if #extension[1] eq 0 then
	return NFelement_to_vector1(f, ground_field[1], ground_field[2]);
    else
	g := NFelement_to_vector1(f, extension[1], extension[2]);
	h := [];
	for i in [1..#g] do
	    h cat:= NFelement_to_vector1(g[i], ground_field[1], ground_field[2]);
	end for;
	return h;
    end if;
end function;

/* changing from absolute to relative representation */
Absolute_to_relative := function(f, ground_field, extension)
    dim := Relative_extension_dimension(ground_field, extension);
    g := [];
    for i in [1..dim[2]] do
	Append(~g,  f[1+(i-1)*dim[3]..i*dim[3]]);
    end for;
    return g;
end function;


/* changing from absolute to relative representation given dim of extension*/
Absolute_to_relative_dim := function(f, dim_extension)
    ground_dim := #f div dim_extension;
    g := [];
    for i in [1..dim_extension] do
	Append(~g,  f[1+(i-1)*ground_dim..i*ground_dim]);
    end for;
    return g;
end function;


Vector_to_Polynomial := function(f, field_sequence, field_exponent, R:basis_q := [], list_primes :=[])
    n := Rank(R);
    N := #f;
    if (field_exponent^n ne N) then
	print "length of f and rank of polynomial ring are incompatible";
	return false;
    else
	Ring_pol := PolynomialRing(RationalField(), n);
	f := Vector_to_tower1(f, field_sequence, field_exponent);
	f := Tower_to_vector(f);
	pol := [];
	for i in [1..N] do
	    e := IndexToExponent(i, n, field_exponent);
	    monom := &*[(Ring_pol.(j))^e[j] : j in [1..n]];
	    Append(~pol, f[i]*monom);
	end for;
	return (R ! (&+ pol));
    end if;
end function;

Vector_to_Polynomial_complex := function(f, field_sequence, field_exponent, R:basis_q := [], list_primes :=[])
    n := Rank(R);
    N := #f;
    if (field_exponent^n ne N) then
	print "length of f and rank of polynomial ring are incompatible";
	return false;
    else
	Ring_pol := PolynomialRing(RationalField(), n);
	f := Vector_to_tower1(f, field_sequence, field_exponent);
	f := Tower_to_vector(f);
	pol := [];
	for i in [1..N] do
	    e := IndexToExponent(i, n, field_exponent);
	    monom := &*[(Ring_pol.(j))^e[j] : j in [1..n]];
	    Append(~pol, f[i]*monom);
	end for;
	return (R ! (&+ pol));
    end if;
end function;


Relative_vector_to_polynomial := function(f, ground_field, extension, R)
    n := Rank(R);
    if n ne (#ground_field[1] + #extension[1]) then
	print "length of f and rank of polynomial ring are incompatible";
	return false;
    elif #extension[1] eq 0 then
	return Vector_to_Polynomial(f, ground_field[1], ground_field[2], R);
    else
	r_ground := #ground_field[1];
	r_ext := #extension[1];
	Ring_pol := PolynomialRing(Rationals(), n);
	g := Relative_vector_to_tower1(f, ground_field, extension);
	g := Tower_to_vector(g);
	g := Vector_to_tower(g, extension[2]^r_ext);
	pol := [];
	for i in [1..extension[2]^r_ext] do
	    e_ext := IndexToExponent(i, r_ext, extension[2]);
	    monom_ext := &*[(Ring_pol.(r_ground+k))^e_ext[k] : k in [1..r_ext]];
	    for j in [1..ground_field[2]^#ground_field[1]] do
		e_ground := IndexToExponent(j, r_ground, ground_field[2]);
		monom_ground := &*[(Ring_pol.(l))^e_ground[l] : l in [1..r_ground]];
		Append(~pol, g[i, j]*monom_ext*monom_ground);
	    end for;
	end for;
	return (R ! (&+ pol));
    end if;
end function;

Relative_swap_field_indexes := function(ground_field, extension)
    basis_ext, basis_ground := Relative_naive_basis(ground_field, extension);
    basis := ElementToSequence(TensorProduct(Vector(basis_ext), Vector(basis_ground)));
    basis_new := ElementToSequence(TensorProduct(Vector(basis_ground), Vector(basis_ext)));
    indexes := [];
    for i in [1..#basis] do
	Append(~indexes, Index(basis_new, basis[i]));
    end for;
    return indexes;
end function;


Relative_swap_field_rep := function(f, ground_field, extension)
    indexes := Relative_swap_field_indexes(ground_field, extension);
    g := ZeroSequence(Rationals(), #indexes);
    for i in [1..#indexes] do
	g[indexes[i]] := f[i];
    end for;
    return g;
end function;


Relative_swap_field_rep_family := function(F, ground_field, extension: size:=1)
    indexes := Relative_swap_field_indexes(ground_field, extension);
    G := [];
    r := size;
    if size gt 1 then
	for j in [1..#F] do
	    g := [ZeroSequence(Rationals(), #indexes) : i in [1..r]];
	    for k in [1..r] do
		for i in [1..#indexes] do
		    g[k][indexes[i]] := F[j][k][i];
		end for;
	    end for;
	    Append(~G, g);
	end for;
    else
	for j in [1..#F] do
	    g := ZeroSequence(Rationals(), #indexes);
	    for i in [1..#indexes] do
		g[indexes[i]] := F[j][i];
	    end for;
    	    Append(~G, g);
	end for;
    end if;
    return G;
end function;


KF_exponentiation := function(list_elements, list_exp, field_sequence, field_exponent:KF:=RationalField())
    if KF eq RationalField() then
	KF := KF_creation(field_sequence, field_exponent);
    end if;
    x := KF!1;
    for i in [1..#list_elements] do
	if list_exp[i] ne 0 then
	    y := Vector_to_NFelement1(list_elements[i], field_sequence, field_exponent:KF:= KF);
	    x *:= y^list_exp[i];
	end if;
    end for;
    return NFelement_to_vector1(x, field_sequence, field_exponent);
end function;


Relative_exponentiation := function(list_elements, list_exp, ground_field, extension:KE:=RationalField())
    if KE eq RationalField() then
	K := Relative_extension_creation(ground_field, extension);
    else
	K := KE;
    end if;
    x := K!1;
    for i in [1..#list_elements] do
	if list_exp[i] ne 0 then
	    x *:= Relative_vector_to_NFelement1(list_elements[i], ground_field, extension:KE:= K)^list_exp[i];
	end if;
    end for;
    return Relative_NFelement_to_vector1(x, ground_field, extension);
end function;


/* Given f, return its image mod q */
Reduce := function(f, F_q)
    return ChangeUniverse([f[i] : i in [1..#f]], F_q);
end function;


Reduce_finite_field := function(f, q, k)
    F_q_k := GF(q, k);
    return [F_q_k ! f[i] : i in [1..#f]], F_q_k;
end function;


/* naive QQ-basis in finite field */
KF_naive_basis_q := function(field_sequence, field_exponent, F_q)
    basis_sequence := [];
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    field_sequence_q := [Root(F_q!field_sequence[i], field_exponent) : i in [1..field_length]];
    for i in [1..field_dim] do
	e := IndexToExponent(i, field_length, field_exponent);
	Append(~basis_sequence, &*[field_sequence_q[j]^e[j] : j in [1..field_length]]);
    end for;
    return basis_sequence;
end function;


/* naive QQ-basis in finite field -- relative version 
q is supposed to be a good prime for both extensions */
// CAREFUL : ONLY KUMMER ARE SUPPORTED
Relative_naive_basis_q := function(ground_field, extension, F_q)
    basis_ground := KF_naive_basis_q(ground_field[1], ground_field[2], F_q);
    basis_ext := KF_naive_basis_q(extension[1], extension[2], F_q);
    return ElementToSequence(TensorProduct(Vector(basis_ext), Vector(basis_ground)));
end function;


/* embedding of basis mod q ; field_sequence verifies power conditions [1,...,1] mod q  */
KF_reduce_basis_q := function(field_sequence, field_exponent, F_q: basis_vector:=[])
    if #basis_vector ne 0 then
	basis := basis_vector;
    else
	basis := KF_naive_basis(field_sequence, field_exponent);
	//basis;
    end if;
    //F_q := GF(q, 1);
    return [Root(F_q!basis[i], field_exponent) : i in [1..#basis]];
end function;


/* embedding of basis mod q ; field_sequence verifies power conditions [1,...,1] mod q  */
KF_naive_basis_q_new := function(field_sequence, field_exponent, F_q: basis_vector:=[])
    field_sequence_q := [Root(F_q!field_sequence[i], field_exponent) : i in [1..#field_sequence]];
    basis_q := Vector([F_q!1]);
    for i in [1..#field_sequence_q] do
	b_q := Vector([ field_sequence_q[i]^j : j in [0..field_exponent-1]]);
	basis_q := TensorProduct(b_q, basis_q);
    end for;
    //F_q := GF(q, 1);
    return (basis_q);
end function;


/* field_sequence is supposed to verify the power conditions [1......1] mod q */
/* Embedding return f viewed as an element of F_q */
Embedding_q := function(f, field_sequence, field_exponent, F_q, basis_q: basis_vector:=[])
    g := Tower_to_vector(Vector_to_tower1(f, field_sequence, field_exponent:basis_q:=basis_vector));     
    g_q := Reduce(g, F_q);
    return InnerProduct(Vector(g_q), basis_q);
end function;


/* field_sequence is supposed to verify the power conditions [1......1] mod q */
Relative_embedding_q := function(f, ground_field, extension, F_q:basis := [])
    if #basis eq 0 then
	basis_q := Relative_naive_basis_q(ground_field, extension, F_q);
    else
	basis_q := basis;
    end if;
    g := Tower_to_vector(Relative_vector_to_tower1(f, ground_field, extension));     
    g := Reduce(g, F_q);
    return InnerProduct(ChangeRing(Vector(g), F_q), ChangeRing(Vector(basis_q), F_q));
end function;

Relative_list := function(list, field_sequence, field_exponent)
    rel_list := [];
    beta := ZeroSequence(IntegerRing(), #field_sequence);
    for i in [0..field_exponent-1] do
	beta[#beta] := i;
	index := ExponentToIndex(beta, field_exponent);
	Append(~rel_list, list[index]);
    end for;
    return rel_list;
end function;

/* Creation of the lattice given the family U */
LogLattice_creation := function(U)
    L := Lattice(Matrix([U[i, 2] : i in  [1..#U]]));
    return L;
end function;


KF_simple_fields := function(kummer_field: list:=[])
    list := list;
    field_sequence := kummer_field[1];
    field_exponent := kummer_field[2];
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    INDEX := Index(list, kummer_field);
    if INDEX ne 0 then   //test if KF is in the list already calculated
	return list;
    else
	if (field_length eq 0) then
	    return [];
	elif (field_length eq 1) then      // if KF is a minimal field, calculate the unit group with standard method
	    Include(~list, kummer_field);
	    return list;
	else
	    ms := field_sequence[field_length-1];
	    mt := field_sequence[field_length];
	    m_0 := Prune(Prune(field_sequence));	
	    // Compute the units of the chosen subfields";
	    subfield_sequence := m_0 cat [ms];
	    list := $$(<subfield_sequence, field_exponent>:list:=list);
	    for j in [0..field_exponent-1] do
		subfield_sequence := m_0 cat [ms^j*mt]; /* defines subfield */
		list:= $$(<subfield_sequence, field_exponent>: list:=list);
	    end for;
	    return list;
	end if;
    end if;
end function;

/* ColumnNorm := function(C) */
/* return &+ [AbsoluteValue(C[i]) : i in [1..#C]]; */
/* end function; */


/* MatrixNormColumn := function(M) */
/* return Max([ColumnNorm(ElementToSequence(ColumnSubmatrix(M, i, 1))) : i in [1..Ncols(M)]])  ; */
/* end function; */


/* MatrixNormRow := function(M) */
/* return Max([ColumnNorm(ElementToSequence(M[i])) : i in [1..Nrows(M)]])  ; */
/* end function; */


/* GSO := function(M) */
/*     n := Nrows(M); m := Ncols(M); */
/*     N := M; */
/*     for i in [1..n] do */
/* 	for j in [1..i-1] do */
/* 	    N[i] := N[i] - (InnerProduct(M[i], N[j])/ Norm(N[j]))*N[j]; */
/* 	end for; */
/*     end for; */
/*     return N; */
/* end function; */


Sort_Vectornorm := procedure(~V)
    N := [Norm(Vector(V[i,1])) : i in [1..#V]];
    ParallelSort(~N, ~V);
end procedure;


Sort_Lognorm := procedure(~V)
    N := [Norm(Vector(V[i,2])) : i in [1..#V]];
    ParallelSort(~N, ~V);
end procedure;


/* remove units equal to 1 or -1  and multiples*/
Family_purge := function(U, dimension)
    V := [];			/* will reduce new family */
    indexes := [];
    T := [RationalField()!1];
    Tminus := [Rationals()!-1];
    Z := ZeroSequence(RationalField(), dimension -1);
    T := T cat Z;
    Tminus := Tminus cat Z;
    Z1 := ZeroSequence(RationalField(), dimension);
    r := #U;
    /* if dimension mod 2 ne 0 then */
    for i in [0..r-1] do
	if ((U[r-i,1] eq T) or (U[r-i,1] eq Tminus) or (U[r-i,2] eq Z1)) then
	    Remove(~U, r-i);
	    /* Include(~indexes, i); */
	    /* Append(~V, U[i]); */
	end if;
    end for;
    /* else */
    /*     for i in [1..#U] do */
    /* 	if ((U[i,1] ne T) and (U[i,1] ne Tminus) and (U[i,2] ne Z1)) then */
    /* 	    Append(~V, U[i]); */
    /* 	end if; */
    /*     end for; */
    /* end if; */
    U := SetToSequence(SequenceToSet(U));
    /* Append(~U, [Tminus, Z1]); */
    return U;
end function;


/* Reduction of family U by LLL in Log representation */
Family_reduction := function(U, field_sequence, field_exponent, precision_log: version:="lll")
    U1 := [U[i,1] : i in [1..#U]];
    field_dim := field_exponent^#field_sequence;
    L := KF_creation(field_sequence, field_exponent);
    r := #U;
    M := IdentityMatrix(RationalField(), r);
    N := [U[i,2] : i in [1..r]];
    N := Matrix(N);
    N := HorizontalJoin(M, 2^r*N);
    if version eq "lll" then
	P := LLL(N: Delta:=0.99, Eta:=0.501);
    elif version eq "bkz" then
	P := BKZ(N, 20: Delta:=0.99, Eta:=0.501);
    end if;
    V := ColumnSubmatrixRange(P, 1, r);
    for i in [1..r] do
	RemoveColumn(~P, 1);
    end for;
    P := P/2^r;
    W := [];
    T := [Rationals()!0 : i in [1..field_dim]];
    Tone := [1] cat ZeroSequence(RationalField(), field_dim-1);
    Tminus := [-1] cat ZeroSequence(RationalField(), field_dim-1);
    for j in [1..r] do
	if (ElementToSequence(P[j]) ne T)  then
	    S1 := KF_exponentiation(U1, ChangeUniverse(Eltseq(V[j]), Integers()), field_sequence, field_exponent: KF:=L);
	    S2 := Eltseq(P[j]);
	    Append(~W, [S1, S2]);
	end if;
    end for;
    return W;
end function;


/* Reduction of family U by LLL in Log representation -- relative version  */
Relative_family_reduction := function(U, ground_field, extension, precision_log: version := "lll")
    U1 := [U[i, 1] : i in [1..#U]];   
    field_dim := Relative_extension_dimension(ground_field, extension)[1];
    T := [0 : i in [1..field_dim]];
    Tone := [1] cat ZeroSequence(RationalField(), field_dim-1);
    Tminus := [-1] cat ZeroSequence(RationalField(), field_dim-1);
    T_ONE := [Tminus, T];
    r := #U;
    M := /* 2^field_dim* */IdentityMatrix(RationalField(), r);
    N := [U[i,2] : i in [1..r]];
    N := 2^(field_dim)*Matrix(N);
    N := HorizontalJoin(M, N);
    if version eq "lll" then
	P := LLL(N: Delta:=0.99, Eta:=0.501);
    elif version eq "bkz" then
	P := BKZ(N, 20: Delta:=0.99, Eta:=0.501);
    end if;
    V := ChangeRing(ColumnSubmatrixRange(P, 1, r), Integers());
    for i in [1..r] do
	RemoveColumn(~P, 1);
    end for;
    P := P/2^(field_dim);
    W := [];
    L := Relative_extension_creation(ground_field, extension);
    for j in [1..r] do
	if Eltseq(P[j]) ne T then
	    S1 := Relative_exponentiation(U1, Eltseq(V[j]), ground_field, extension: KE:=L);
	    Append(~W, [S1, Eltseq(P[j])]);
	end if;
    end for;
    return Family_purge(W, field_dim);
end function;


// M is supposed to be sorted?
Babai_decoding := function(M, v)
    N := VerticalJoin(M, Vector(v));
    Z := ZeroSequence(RationalField(), Nrows(N)-1);
    MAX :=  Max([Norm(N[i]) : i in [1..Nrows(N)]]);
    Z := Z cat [MAX];
    N := HorizontalJoin(N, Transpose(Matrix([Z])));
    r := Nrows(N);
    Id := /* 2^field_dim* */IdentityMatrix(RationalField(), r);
    d := Denominator(N);
    /* N := 2^r*N; */
    N := 2^Ceiling(Log(2, MAX))*N;
    N := HorizontalJoin(Id, N);
    N := LLL(N: Delta:=0.75, Eta:=0.501);
    V := ColumnSubmatrixRange(N, 1, r);
    for i in [1..r] do
	RemoveColumn(~N, 1);
    end for;
    /* N := ChangeRing(N, Rationals())/(2^r); */
    N := ChangeRing(N, Rationals())/(2^Ceiling(Log(2, MAX)));
    for i in [1..r] do
	if N[i, Ncols(N)] ne 0 then
	    i0 := i;
	end if;
    end for;
    w := ElementToSequence(N[i0]);
    Prune(~w);
    return w, ChangeUniverse(ElementToSequence(V[i0]), Integers());
end function;


Power_Logreduction_vector := function(v, Upow, field_sequence, field_exponent)
    K := KF_creation(field_sequence, field_exponent: Check:=false);
    LogUnit := Matrix([Upow[i, 2] : i in [1..#Upow]]);
    v1 := v[1]; v2 := v[2];
    w2, relations := Babai_decoding(LogUnit, v2);
    Upow1 := [Upow[i,1] : i in [1..#Upow]];
    w1 := KF_exponentiation(Upow1 cat [v1], relations, field_sequence, field_exponent: KF:=K);
    delete K;
    return [w1, w2];
end function;


Relative_power_Logreduction_vector := function(v, Upow, ground_field, extension, exponent)
    K := Relative_extension_creation(ground_field, extension);
    LogUnit := Matrix([Upow[i, 2] : i in [1..#Upow]]);
    v1 := v[1]; v2 := v[2];
    w2, relations := Babai_decoding(LogUnit, v2);
    Upow1 := [Upow[i,1] : i in [1..#Upow]];
    w1 := Relative_exponentiation(Upow1 cat [v1], relations, ground_field, extension: KE:=K);
    delete K;
    return [w1, w2];
end function;

Power_Logreduction := function(V, U, field_sequence, field_exponent: red_version := "lll")
    W := [];
    Upow := [];
    for i in [1..#U] do
	power := [NFelement_to_vector1(Vector_to_NFelement1(U[i,1], field_sequence, field_exponent)^field_exponent, field_sequence, field_exponent), ElementToSequence(Vector(U[i,2])*field_exponent)];
	Append(~Upow, power);
    end for;
    print "powers created";
    Sort_Lognorm(~Upow);
    Upow := Family_reduction(Upow, field_sequence, field_exponent, 1: version := red_version);
    for i in [1..#V] do
	time w := Power_Logreduction_vector(V[i], Upow, field_sequence, field_exponent);
	Norm_w := Norm(Vector(w[1]));
	Norm_V := Norm(Vector(V[i,1]));
	if Norm_w lt Norm_V then
	    Append(~W, w);
	else
	    Append(~W, V[i]);
	end if;
	Append(~Upow, w);
	Sort_Lognorm(~Upow);
    end for;
    delete Upow;
    return W;
end function;


Relative_power_Logreduction := function(V, U, ground_field, extension, exponent)
    W := [];
    Upow := [];
    for i in [1..#U] do
	power := [Relative_NFelement_to_vector1(Relative_vector_to_NFelement1(U[i,1], ground_field, extension)^exponent, ground_field, extension), ElementToSequence(Vector(U[i,2])*exponent)];
	Append(~Upow, power);
    end for;
    Sort_Lognorm(~Upow);
    Upow := Relative_family_reduction(Upow, ground_field, extension, 1);
    for i in [1..#V] do
	w := Relative_power_Logreduction_vector(V[i], Upow, ground_field, extension, exponent);
	Norm_w := Norm(Vector(w[1]));
	Norm_V := Norm(Vector(V[i,1]));
	if Norm_w lt Norm_V then
	    Append(~W, w);
	    print "vector replaced";
	else
	    Append(~W, V[i]);
	end if;
	Append(~Upow, w);
	Sort_Lognorm(~Upow);
    end for;
    delete Upow;
    return W;
end function;



Orthogonal_projection := function(f, g)
    f_scalar := InnerProduct(Vector(f), Vector(g))/Norm(Vector(g));
    return Eltseq(Vector(f)-f_scalar*Vector(g));
end function;


Test_units_power := function(h, U, exponent, ground_field, extension)
    bool := false;
    K := Relative_extension_creation(ground_field, extension);
    V := VectorSpace(GF(exponent), #U);
    h1 := Relative_vector_to_NFelement1(h, ground_field, extension:KE:=K);
    count := 0;
    number := exponent^#U;
    for v in V do
	count +:= 1;
	print count, " over ", number;
	u := &* [Relative_vector_to_NFelement1(U[i,1], ground_field, extension:KE:=K)^(Integers()!v[i]) : i in [1..#U]];
	b := IsPower(h1*u, exponent); ;
	bool or:= b;
    end for;
    return bool;
end function;
