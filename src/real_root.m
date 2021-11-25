/* evaluate the needed precision for set U */
Precision_evaluation := function(field_sequence, field_exponent, U)
    norms := [];
    for i in [1..#U] do
	Append(~norms, Ceiling((field_exponent)^(#field_sequence-1)*Log(Norm(Vector(U[i])))));
    end for;
    return Max(norms);
end function;

/* relative precision evaluation */
Relative_precision_evaluation := function(ground_field, extension, U)
    dim := Relative_extension_dimension(ground_field, extension);
    e := Min([ground_field[2], extension[2]]);
    prec := [];
    for i in [1..#U] do
	Append(~prec, Ceiling(dim[1]*Log(2+Norm(Vector(U[i])))/e));
    end for;
    return Max(prec);
end function;


// Compute Lattice defined by d with precision l given Unitary matrix SeqUni
// corresponding to precision l' < l
Real_basis_lattice := function(basis_free, field_exponent, precision, SeqUni)
    ZZ := IntegerRing();
    field_dim := #basis_free;
    Coeff := (field_dim - 1)*(2 + field_dim) div 4;
    real_basis := KF_real_basis_embedding(basis_free, field_exponent, precision);
    RealBasis := ChangeUniverse([Round(2^(precision)*real_basis[i]) : i in [1..#real_basis]], Integers());
    RealBasis := -Vector(RealBasis);
    M := Coeff*IdentityMatrix(Integers(), field_dim);
    M := HorizontalJoin(Transpose(Matrix(RealBasis)), M);
    M := SeqUni*M;
    A := LLL(M);
    V := ChangeRing(ColumnSubmatrixRange(A, 2, field_dim+1), Rationals());
    V := ChangeRing(V/Coeff, Integers());
    SeqUni := V;
    return A, ChangeRing(SeqUni, Integers()), real_basis;
end function;


// Compute Lattice defined by d with precision l given Unitary matrix SeqUni corresponding to precision l' < l
// relative version : CAREFUL ONLY KUMMER SUPPORTED
Relative_real_basis_lattice := function(ground_field, extension, precision, SeqUni)
    ZZ := IntegerRing();
    field_dim := Relative_extension_dimension(ground_field, extension)[1];
    /* Coeff := field_dim div 2; */
    Coeff := (field_dim - 1)*(2 + field_dim) div 4;
    basis_ext, basis_ground := Relative_real_basis_embedding(ground_field, extension, precision);
    if #basis_ext eq 0 then
	real_basis := basis_ground;
    elif #basis_ground eq 0 then
	real_basis := basis_ext;
    else
	real_basis := ElementToSequence(TensorProduct(Vector(basis_ext), Vector(basis_ground)));
    end if;
    realBasis := ChangeUniverse([Round(2^(precision)*real_basis[i]) : i in [1..#real_basis]], Integers());
    realBasis := -Vector(realBasis);
    M := Coeff*IdentityMatrix(Integers(), field_dim);
    M := HorizontalJoin(Transpose(Matrix(realBasis)), M);
    M := SeqUni*M;
    A := LLL(M);
    V := ChangeRing(ColumnSubmatrixRange(A, 2, field_dim+1), Rationals());
    V := ChangeRing(V/Coeff, Integers());
    SeqUni := V*SeqUni;
    return A, SeqUni;
end function;


/* initialize lattice at precision 1 */
Real_basis_lattice_init := function(basis_free, field_sequence, field_exponent)
    SeqUni := IdentityMatrix(Integers(), #basis_free);
    return Real_basis_lattice(basis_free, field_exponent, 1, SeqUni);
end function;


/* initialize lattice at precision 1 -- relative version */
Relative_real_basis_lattice_init := function(ground_field, extension)
    dim := Relative_extension_dimension(ground_field, extension);
    SeqUni := IdentityMatrix(Integers(), dim[1]);
    return Relative_real_basis_lattice(ground_field, extension, 1, SeqUni);
end function;


Test_decode := function(x, basis_lattice, field_sequence, field_exponent, precision)
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    /* Coeff := field_dim div 2; */
    Coeff := (field_dim - 1)*(2 + field_dim) div 4;
    /* Coeff := 2^(precision div 2); */
    y := Round((2^(precision))*x);
    Z := ZeroSequence(Integers(), field_dim+1);
    Z[1] := y;
    /* print "Z dim: ", #Z; */
    /* print "basis dim: ", Ncols(basis_lattice); */
    M := VerticalJoin(ChangeRing(basis_lattice, Integers()), Matrix(Vector(Z)));
    Z[1] := 0;
    Z[field_dim+1] := (y);
    M := HorizontalJoin(M, Transpose(Matrix(Vector(Z))));
    M := LLL(M);
    x := ElementToSequence(ChangeRing(M[field_dim+1], RationalField())/Coeff);
    x := x[2..field_dim+1];
    return ElementToSequence(Vector(x));
end function;


/* decode with lattice -- relative version 
CAREFUL : ONLY KUMMER SUPPORTED   */
Relative_test_decode := function(x, basis_lattice, ground_field, extension, precision)
    field_dim := Relative_extension_dimension(ground_field, extension)[1];
    Coeff := (field_dim - 1)*(2 + field_dim) div 4;
    y := Round((2^(precision))*x);
    Z := ZeroSequence(Integers(), field_dim+1);
    Z[1] := y;
    M := VerticalJoin(ChangeRing(basis_lattice, Integers()), Matrix(Vector(Z)));
    Z[1] := 0;
    m_norm := Max([Norm(M[i]) : i in [1..Nrows(M)]]);
    Z[field_dim+1] := y;
    M := HorizontalJoin(M, Transpose(Matrix(Vector(Z))));
    M := LLL(M);
    x := ElementToSequence(ChangeRing(M[field_dim+1], RationalField())/Coeff);
    x := x[2..field_dim+1];
    return ElementToSequence(Vector(x));
end function;


// goes from precision "precision" to precision "precision*q^k"  with step q
Real_basis_lattice_update_geom := function(basis_free, field_exponent, precision, q, k, lattice, uni, real_basis)
    for i in [1..k] do
	precision := Ceiling(precision*q);
	lattice, uni, real_basis := Real_basis_lattice(basis_free, field_exponent, precision, uni);
    end for;
    return lattice, uni, real_basis;
end function;


// goes from precision "precision" to precision "precision*q^k"  with step q -- relative version
Relative_real_basis_lattice_update_geom := function(ground_field, extension, precision, q, k, lattice, uni)
    for i in [1..k] do
	print i, "over", k;
	precision := Ceiling(precision*q);
	lattice, uni := Relative_real_basis_lattice(ground_field, extension, precision, uni);
    end for;
    return lattice, uni;
end function;


Real_root_rec := function(f, basis_free, field_sequence, field_exponent, precision, basis_lattice, uni:real_basis := [])
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    x := KF_real_embedding(f, field_sequence, field_exponent, precision, basis_free:real_basis:=real_basis);
    x := Root(RealField(precision)!x, field_exponent);
    K := KF_creation(field_sequence, field_exponent);
    s := Cputime();
    g := Test_decode(x, basis_lattice, field_sequence, field_exponent, precision);
    print "first attempt to compute the root done in", Cputime(s);
    t := Vector_to_NFelement1(f, field_sequence, field_exponent:KF:=K) eq Vector_to_NFelement1(g, field_sequence, field_exponent:KF:=K)^field_exponent;
    while t eq false do
	s := Cputime();
	precision := Ceiling(Sqrt(2)*precision);
	basis_lattice, uni, real_basis := Real_basis_lattice(basis_free, field_exponent, precision, uni);
	print "Update of the lattice done in", Cputime(s);
	s := Cputime();
	x := KF_real_embedding(f, field_sequence, field_exponent, precision, basis_free:real_basis:=real_basis);
	x := Root(RealField(precision)!x, field_exponent);
	g := Test_decode(x, basis_lattice, field_sequence, field_exponent, precision);
	/* print precision; */
	print "another attempt to compute the root done in", Cputime(s);
	t := Vector_to_NFelement1(f, field_sequence, field_exponent:KF:=K) eq Vector_to_NFelement1(g, field_sequence, field_exponent:KF:=K)^field_exponent;
	// print precision;
    end while;
    return g, precision, basis_lattice, uni;
end function;


/* computation of n-th root by real lattice method
reltive case : CAREFUL ONLY KUMMER SUPPORTED   */
Relative_real_root_rec := function(f, ground_field, extension, exponent, precision, basis_lattice, uni:real_basis := [])
    field_dim := Relative_extension_dimension(ground_field, extension)[1];
    x := Relative_real_embedding(f, ground_field, extension, precision);
    x := Root(RealField(precision)!x, exponent);
    s := Cputime();
    g := Relative_test_decode(x, basis_lattice, ground_field, extension, precision);
    print "first attempt to compute the root done in", Cputime(s);
    K := Relative_extension_creation(ground_field, extension);
    t := Relative_vector_to_NFelement1(f, ground_field, extension:KE:=K) eq Relative_vector_to_NFelement1(g, ground_field, extension:KE:=K)^exponent;
    while t eq false do
	s := Cputime();
	precision := Ceiling(Sqrt(2)*precision);
	basis_lattice, uni := Relative_real_basis_lattice(ground_field, extension, precision, uni);
	print "Update of the lattice done in", Cputime(s);
	s := Cputime();
	x := Relative_real_embedding(f, ground_field, extension, precision);
	x := Root(RealField(precision)!x, exponent);
	g := Relative_test_decode(x, basis_lattice, ground_field, extension, precision);
	/* print precision; */
	print "another attempt to compute the root done in", Cputime(s);
	t := Relative_vector_to_NFelement1(f, ground_field, extension:KE:=K) eq Relative_vector_to_NFelement1(g, ground_field, extension:KE:=K)^exponent;
	// print precision;
    end while;
    return g, precision, basis_lattice, uni;
end function;

KF_depth := function(kummer_field: dim:=0)
    dim := dim;
    if dim eq 0 then
	dim := KF_dimension(kummer_field);
    end if;
    if kummer_field[2] gt 7 then
	return 0;
    elif dim lt 15 then
	return 0;
    elif kummer_field[2] in [5,7] then
	return 1;
    elif (dim lt 30) and (kummer_field[2] eq 3) then
	return 1;
    elif (kummer_field[2] eq 3) or (dim lt 30) then
	return 2;
    else
	return 3;
    end if;
end function;


Relative_depth := function(ground_field, extension)
    dim := Relative_extension_dimension(ground_field, extension)[1];
    d_g := Min(KF_depth(ground_field: dim:=dim), #ground_field[1]);
    d_r := Min(KF_depth(extension: dim:=dim), #extension[1]);
    if ground_field[2]^d_g gt extension[2]^d_r then
	return 0, d_g;
    else
	return 1, d_r;
    end if;
end function;


KF_action_conjugate := function(v, kummer_field, depth, list_conj)
    act := ZeroSequence(Integers(), kummer_field[2]^depth);
    for i in [1..(kummer_field[2]^depth-1) div 2] do
	act[list_conj[i,1]] := Integers()!v[i];
	act[list_conj[i,2]] := Integers()!((kummer_field[2]-1)*v[i]);
    end for;
    return act;
end function;

Possible_action_list := function(field_exponent, list_conj: depth:=1)
    list :=[];
    if field_exponent eq 2 then
	V := VectorSpace(GF(field_exponent), field_exponent^depth-1);
	for v in V do
	    Append(~list, ChangeUniverse([0] cat ElementToSequence(v), IntegerRing()));
	end for;
    else
	V := VectorSpace(GF(field_exponent), (field_exponent^depth-1) div 2);
	count:=0;
	for v in V do
	    count+:=1;
	    if count mod 1000 eq 0 then print count, " over ", #V; end if;
	    act := ZeroSequence(Integers(), field_exponent^depth);
	    for i in [1..(field_exponent^depth-1) div 2] do
		act[list_conj[i,1]] := Integers()!v[i];
		act[list_conj[i,2]] := Integers()!((field_exponent-1)*v[i]);
	    end for;
	    Append(~list, act);
	end for;
    end if;
    return list;
end function;

KF_decode_partial_mink := function(part_mink, sub_basis_lattice, rel_basis_free, rel_real_basis, field_sequence, field_exponent, precision, zeta: depth:=1, field:=Rationals())
    field_length := #field_sequence;
    rel_mink := ChangeUniverse(part_mink, field);
    v := Complex_Minkowski_to_vector(rel_mink, rel_basis_free, [field_sequence[field_length-depth+1..field_length]], field_exponent, precision, zeta);
    test := [];
    for j in [1..#v] do
	test cat:= Test_decode(Real(v[j]), sub_basis_lattice, field_sequence[1..field_length-depth], field_exponent, precision);
    end for;
    return test, v;
end function;

KF_decode_embedding_part := function(part_emb, sub_basis_lattice, field_sequence, field_exponent, precision: depth:=1, known_ind := 0, known_part := [])
    field_length := #field_sequence;
    test := [];
    for j in [1..#part_emb] do
	if j eq known_ind then
	    test cat:= known_part;
	else
	    test cat:= Test_decode(Real(part_emb[j]), sub_basis_lattice, field_sequence[1..field_length-depth], field_exponent, precision);
	end if;
    end for;
    return test;
end function;


Relative_decode_embedding_part := function(part_emb, ground_field, extension, real_lattice, precision, depth: start_ind := 1)
    ext2 := <extension[1][1..#extension[1]-depth], extension[2]>;
    test := [];
    for j in [start_ind..#part_emb] do
	test := test cat Relative_test_decode(Real(part_emb[j]), real_lattice, ground_field, ext2, precision);
    end for;
    return test;
end function;


KF_test_one_coord_emb := function(x_emb, norm_test, sub_basis_lattice, field_sequence, field_exponent, precision: depth:=1, index:=1)
    field_length := #field_sequence;
    x_ind := Test_decode(Real(x_emb), sub_basis_lattice, field_sequence[1..field_length-depth], field_exponent, precision);
    norm_quo := Norm(Vector(x_ind))/norm_test;
    if norm_quo lt 10^-2 then
	return true, 1, x_ind;
    elif norm_quo gt 10^2 then
	return true, 0, x_ind;
    else
	return false, 0, norm_quo;
    end if;
end function;


Relative_test_one_coord_emb := function(x_emb, norm_test, basis_lattice, ground_field, extension, precision: depth:=1, index:=1, exp:=1)
    ext := <extension[1][1..#extension[1]-depth], extension[2]>;
    x_ind := Relative_test_decode(Real(x_emb), basis_lattice, ground_field, ext, precision);
    norm_quo := Norm(Vector(x_ind))/norm_test;
    if norm_quo lt 10^(-exp) then
	return true, 1, x_ind;
    elif norm_quo gt 10^exp then
	return true, 0, x_ind;
    else
	return false, 0, norm_quo;
    end if;
end function;


Relative_decode_partial_mink := function(part_mink, ground_field, extension, real_lattice, precision, zeta, depth)
    ext1 := <extension[1][#extension[1]-depth+1..#extension[1]], extension[2]>;
    ext2 := <extension[1][1..#extension[1]-depth], extension[2]>;
    v := Relative_complex_minkowski_to_vector(part_mink, ground_field, ext1, precision, zeta);
    test := [];
    for j in [1..#v] do
	test := test cat Relative_test_decode(Real(v[j]), real_lattice, ground_field, ext2, precision);
    end for;
    return test;
end function;


KF_test_root_from_partial := function(f, part_mink, kummer_field, exponent, real_lattice, rel_basis_free, rel_real_basis, precision, zeta, depth, list_conj)
    CC := Universe(part_mink);
    if kummer_field[2] ne 2 then
	length_rel := (kummer_field[2]^depth-1) div 2;
    else
	length_rel := (kummer_field[2]^depth-1) ;
    end if;
    V := VectorSpace(GF(exponent), length_rel);
    mink := KF_complex_mink_from_half(part_mink, kummer_field[1], kummer_field[2], depth, list_conj);
    vect0 := Complex_Minkowski_to_vector(mink, rel_basis_free, kummer_field[1][#kummer_field[1]-depth+1..#kummer_field[1]], kummer_field[2], precision, zeta: real_free_basis:=rel_real_basis);
    norm_test := 0;
    index_test := 0;

    while norm_test eq 0 do
	index_test := (index_test +1);
	x0_0 := Test_decode(Real(vect0[index_test]), real_lattice, kummer_field[1][1..#kummer_field[1]-depth], kummer_field[2], precision);
	norm_test := Norm(Vector(x0_0));
    end while;

    count:=0;
    for v in V do
	count+:=1;
	if count mod 1000 eq 0 then
	    print count, " over ", #V;
	end if;
	Z := Vector([1] cat [CC!zeta^(Integers()!v[i]) : i in [1..length_rel]]);
	mink := Eltseq(Z*Vector(part_mink));
	mink := KF_complex_mink_from_half(mink, kummer_field[1], kummer_field[2], depth, list_conj);
	xv_test := Complex_coefficient_from_minkowski(mink, index_test, rel_real_basis, kummer_field[1][#kummer_field[1]-depth+1..#kummer_field[1]], kummer_field[2], precision, zeta);
	bool_test_one, ind_test, root_0 := KF_test_one_coord_emb(Real(xv_test), norm_test, real_lattice, kummer_field[1], kummer_field[2], precision: depth:=depth);
	if bool_test_one then
	    if ind_test eq 0 then
		v_root := vect0;
		x0 := x0_0;
	    else
		v_root := Complex_Minkowski_to_vector(mink, rel_basis_free, kummer_field[1][#kummer_field[1]-depth+1..#kummer_field[1]], kummer_field[2], precision, zeta: real_free_basis:=rel_real_basis);
		x0 := root_0;
	    end if;
	    root_test := KF_decode_embedding_part(v_root, real_lattice, kummer_field[1], kummer_field[2], precision: depth:=depth, known_ind := index_test, known_part := x0);
	    bool := NFelement_to_vector1(Vector_to_NFelement1(root_test, kummer_field[1], kummer_field[2])^exponent, kummer_field[1], kummer_field[2]) eq f;
	    if bool then
		return bool, root_test;
	    end if;
	end if;
    end for;
    return false, f;
end function;


Relative_test_root_from_partial_new := function(f, partial_mink, ground_field, extension, exponent, real_lattice, precision, list_indexes_conjugates, depth: exp:=0)
    CC := ComplexField(precision);
    zeta_exponent := CC!RootOfUnity(exponent);
    zeta_ext := CC!RootOfUnity(extension[2]);
    sub_ext := <extension[1][1..#extension[1]-depth], extension[2]>;
    rel_ext := <extension[1][#extension[1]-depth+1..#extension[1]], extension[2]>;
    rel_real_basis := KF_real_basis_embedding(KF_primefree_basis(rel_ext[1], rel_ext[2]:list_primes := []), rel_ext[2], precision);
    exp := exp;

    if extension[2] ne 2 then
	length_rel := (extension[2]^depth-1) div 2;
    else
	length_rel := (extension[2]^depth-1);
    end if;

    real_basis := [];
    V := VectorSpace(GF(exponent), length_rel);
    mink := KF_complex_mink_from_half(partial_mink, extension[1], extension[2], depth, list_indexes_conjugates);
    vect0, real_basis := Relative_complex_minkowski_to_vector(mink, ground_field, rel_ext, precision, zeta_ext: real_basis:=real_basis);
    norm_test := 0;
    index_test := 0;
    
    while norm_test eq 0 do
	index_test +:= 1; 
	x0_0 := Relative_test_decode(Real(vect0[index_test]), real_lattice, ground_field, sub_ext, precision);
	norm_test := Norm(Vector(x0_0));
    end while;

    for i_exp in [1..3] do	
	count := 0;
	for v in V do
	    count +:= 1;
	    if count mod 1000 eq 0 then print count, #V; end if;
	    Z := ChangeUniverse([1] cat [zeta_exponent^(Integers()!v[j]) : j in [1..length_rel]], CC);
	    mink := ElementToSequence(Vector(ChangeUniverse(partial_mink, CC))*Vector(Z));
	    mink := KF_complex_mink_from_half(mink, extension[1], extension[2], depth, list_indexes_conjugates);
	    xv_test := Complex_coefficient_from_minkowski(mink, index_test, rel_real_basis, rel_ext[1], rel_ext[2], precision, zeta_ext);
	    bool_test_one, ind_test, root_0 := Relative_test_one_coord_emb(Real(xv_test), norm_test, real_lattice, ground_field, extension, precision: depth:=depth, exp:=exp, index:=index_test);
	    if bool_test_one then
		if ind_test eq 0 then
		    v_root := vect0;
		    x0 := x0_0;
		else
		    v_root := Relative_complex_minkowski_to_vector(mink, ground_field, rel_ext, precision, zeta_ext: real_basis:=real_basis);
	    	    x0 := root_0;
		end if;
		root_test := Relative_decode_embedding_part(v_root, ground_field, extension, real_lattice, precision, depth: start_ind := 1);
		
		bool := Relative_NFelement_to_vector1(Relative_vector_to_NFelement1(root_test, ground_field, extension)^exponent, ground_field, extension) eq f;
		if bool then
		    return bool, root_test;
		end if;
	    end if;
	end for;
	exp := exp - 10 ;
    end for;
    return false, f;
end function;


Relative_test_root_from_partial := function(f, partial_mink, ground_field, extension, exponent, real_lattice, precision, list_indexes_conjugates, depth)
    if extension[2] ne 2 then
	V := VectorSpace(GF(exponent), (extension[2]^depth-1) div 2);
	CC := ComplexField(precision);
	zeta_exponent := CC!RootOfUnity(exponent);
	zeta_ext := CC!RootOfUnity(extension[2]);
	count := 1;
	for v in V do
	    act := ZeroSequence(Integers(), extension[2]^depth);
	    for i in [1..(extension[2]^depth-1) div 2] do
		act[list_indexes_conjugates[i,1]] := Integers()!v[i];
		act[list_indexes_conjugates[i,2]] := Integers()!(exponent-1)*v[i];
	    end for;
	    count+:=1;
	    Z := ChangeUniverse([zeta_exponent^act[j] : j in [1..#act]], CC);
	    part_mink := ElementToSequence(Vector(ChangeUniverse(partial_mink, CC))*Vector(Z));
	    root_test := Relative_decode_partial_mink(part_mink, ground_field, extension, real_lattice, precision, zeta_ext, depth);
	    b := Relative_NFelement_to_vector1(Relative_vector_to_NFelement1(root_test, ground_field, extension)^exponent, ground_field, extension) eq f;
	    if b then
		return b, root_test;
	    end if;
	end for;
    else
	V := VectorSpace(GF(exponent), (extension[2]^depth-1));
	CC := ComplexField(precision);
	zeta_exponent := CC!RootOfUnity(exponent);
	zeta_ext := CC!RootOfUnity(extension[2]);
	for v in V do
	    act := [0] cat Eltseq(ChangeRing(v, Integers()));
	    Z := ChangeUniverse([zeta_exponent^act[j] : j in [1..#act]], CC);
	    part_mink := Eltseq(Vector(ChangeUniverse(partial_mink, CC))*Vector(Z));
	    root_test := Relative_decode_partial_mink(part_mink, ground_field, extension, real_lattice, precision, zeta_ext, depth);
	    b := Relative_NFelement_to_vector1(Relative_vector_to_NFelement1(root_test, ground_field, extension)^exponent, ground_field, extension) eq f;
	    if b then
		return b, root_test;
	    end if;
	end for;
    end if;
    return false, f;
end function;


KF_real_root_rec_depth := function(f, exponent, basis_free, kummer_field, basis_lattice, uni, precision: real_basis := [], depth:=1)
    field_sequence := kummer_field[1];
    field_exponent := kummer_field[2];
    T := Cputime();
    /* #############  basis creations ############ */
    sub_basis_free := KF_primefree_basis(field_sequence[1..#field_sequence-depth], field_exponent);
    diff_basis, rel_basis_free := KF_diff_basis(<field_sequence, field_exponent>, depth);
    /* creation of list on conjugates indexes */
    list_conj := List_indexes_conjugates(depth, field_exponent);
    /* ###########      Start the computation of root      #############*/
    test := false;
    while (not test) do
	precision_float := precision div 3;	/* float structure creation */
	CC<i> := ComplexField(precision_float);
	RR := RealField(precision_float);
	zeta := CC!RootOfUnity(field_exponent);
	rel_real_basis := [RR!Root(RR!rel_basis_free[i], exponent) : i in [1..#rel_basis_free]];
	/* ### computing partial / relative mink embedding of power then root #### */
	part_mink := KF_partial_complex_minkowski(f, field_sequence, field_exponent, precision_float: depth:=depth, zeta:=zeta, list_conj_pairs:=list_conj);
	part_mink := [RR!Root(RR!part_mink[1], exponent)] cat [CC!Root(CC!part_mink[i], exponent) : i in [2..#part_mink]];
	/* ####### Try to find a root with the given precision ####### */
	test, f_r := KF_test_root_from_partial(f, part_mink, kummer_field, exponent, basis_lattice, rel_basis_free, rel_real_basis, precision, zeta, depth, list_conj);
	if (not test) then
            precision := Ceiling(Sqrt(2)*precision);
	    basis_lattice, uni := Real_basis_lattice(sub_basis_free, field_exponent, precision, uni);
	end if;
    end while;
    return f_r, precision, basis_lattice, uni; 
end function;


Relative_real_root_rec_depth := function(f, ground_field, extension, exponent, precision, depth, basis_lattice, uni)
    test := false;
    while test eq false do
	precision_float := precision div 3;
	RR := RealField(precision_float);
	CC := ComplexField(precision_float);
	/* Compute partial mink of power */
	mink_power_part, zeta_ext, list_conj := Relative_partial_complex_minkowski(f, ground_field, extension, precision_float: depth:=depth, zeta:=1, list_conj_pairs := []);
	/* compute roots of partial mink of power */
	mink_part := [RR!Root(RR!mink_power_part[1], exponent)] cat [CC!Root(CC!mink_power_part[i], exponent) : i in [2..#mink_power_part]];
	test, root_test := Relative_test_root_from_partial_new(f, mink_part, ground_field, extension, exponent, basis_lattice, precision, list_conj, depth);
	
	if (not test) then
            s := Cputime();
	    precision := Ceiling(Sqrt(2)*precision);
	    ext := <extension[1][1..(#extension[1]-depth)], extension[2]>;
	    basis_lattice, uni := Relative_real_basis_lattice(ground_field, ext, precision, uni);
	    print "Update of the lattice done in", Cputime(s);
	end if;
    end while;
    return root_test, basis_lattice, uni, precision;
end function;

Relative_real_root_family_depth := function(U, ground_field, extension, exponent: depth:=1, precision:=1, basis_lattice:=1, unitary:=1)
    field_dim := Relative_extension_dimension(ground_field, extension)[1];
    sub_ext := <extension[1][1..#extension[1]-depth], extension[2]>;
    if precision ne 1 then
	real_lattice := basis_lattice;
	prec := precision;
	uni := unitary;
    else
	real_lattice, uni := Relative_real_basis_lattice_init(ground_field, sub_ext);
	prec := 1;
    end if;
    V := [ElementToSequence((field_dim)^exponent*Vector(U[i])) : i in [1..#U]];
    R := [];
    print "COMPUTING ROOTS WITH DEPTH ", depth, " WITH EXTENSION ", extension;
    for i in [1..#V] do
	print "Norm of power is: ", Log(2, Norm(Vector(V[i])));
	prec_new := Ceiling(Max(prec, Round(Relative_precision_evaluation(ground_field, sub_ext, [V[i]])) div 2 ));
	t := Cputime();
	if prec_new gt prec then
	    real_lattice, uni := Relative_real_basis_lattice(ground_field, sub_ext, prec_new, uni);
	end if;
	print "real lattice updated in", Cputime(t), "secondes";
	g, real_lattice, uni, prec := Relative_real_root_rec_depth(V[i], ground_field, extension, exponent, prec_new, depth, real_lattice, uni);
	Append(~R, ElementToSequence(Vector(g)/( field_dim)));
	print i, "TH ROOT COMPUTED IN", Cputime(t);
    end for;
    return R, prec, real_lattice, uni;
end function;



/* ###########  ROOTS OF FAMILY - KF VERSION ############## */
Real_root_family_depth := function(U, field_sequence, field_exponent, basis_free: precision:=1, lattice:=1, unitary := 1, depth := 1, bool := false, exponent:=field_exponent)
    subfield_sequence := field_sequence[1..#field_sequence-depth];

    sub_basis_free := KF_primefree_basis(subfield_sequence, field_exponent);
    field_dim := field_exponent^(#field_sequence);
    t := Cputime();
    C := field_dim;
    V := [ElementToSequence((C^exponent)*Vector(U[i])) : i in [1..#U]];
    sublattice, uni, real_basis := Real_basis_lattice_init(sub_basis_free, subfield_sequence, field_exponent);
    prec := 1;

    if bool eq true then
	prec := precision;
	sublattice := lattice;
	uni := unitary;
    end if;
    CR := [];
    for i in [1..#V] do

	precision_new := Max(prec, Precision_evaluation(subfield_sequence, field_exponent, [V[i]]));
	print precision_new;
	t := Cputime();

	if precision_new gt prec then
	    sublattice, uni := Real_basis_lattice(sub_basis_free, field_exponent, precision_new, uni);
	end if;

	print "Lattice updated in", Cputime(t), "secondes";
	
	t := Cputime();
	g, prec, sublattice, uni := KF_real_root_rec_depth(V[i], exponent, basis_free, <field_sequence, field_exponent>, sublattice, uni, precision_new: real_basis := [], depth:=depth);
	Append(~CR, ElementToSequence(Vector(g)/C));
	print "precision is: ", prec;
	print i, "TH ROOT COMPUTED IN", Cputime(t);
    end for;
    return CR, prec, sublattice, uni;
end function;

/* if can't go to subfields - KF version */
Real_root_family := function(U, field_sequence, field_exponent, basis_free: precision:=1, lattice:=1, unitary := 1, bool := false)
    if #U eq 0 then return [], precision, lattice, unitary; end if;
    subfield_sequence := field_sequence[1..#field_sequence];
    sub_basis_free := basis_free;
    field_dim := field_exponent^(#field_sequence);
    t := Cputime();
    C := field_dim;
    V := [ElementToSequence((C^field_exponent)*Vector(U[i])) : i in [1..#U]];
    sublattice, uni, real_basis := Real_basis_lattice_init(sub_basis_free, subfield_sequence, field_exponent);
    prec := 1;
    if bool eq true then
	prec := precision;
	sublattice := lattice;
	uni := unitary;
    end if;
    CR := [];
    for i in [1..#V] do	
	precision_new := Max(prec, Precision_evaluation(subfield_sequence, field_exponent, [V[i]]));
	t := Cputime();
	if precision_new gt prec then
	    sublattice, uni := Real_basis_lattice(sub_basis_free, field_exponent, precision_new, uni);
	end if;
	print "Basis lattice updated in", Cputime(t), "secondes";
	t := Cputime();
	g, prec, sublattice, uni := Real_root_rec(V[i], basis_free, field_sequence, field_exponent, precision_new, sublattice, uni);
	Append(~CR, ElementToSequence(Vector(g)/C));
	print "precision is: ", prec;
	print i, "TH ROOT COMPUTED IN", Cputime(t);
    end for;
    return CR, prec, sublattice, uni;
end function;
