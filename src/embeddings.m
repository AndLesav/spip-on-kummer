KF_real_basis_embedding := function(basis_free, field_exponent, precision_float)
    real_basis := [];
    RR := RealField(precision_float);
    for i in [1..#basis_free] do
	Append(~real_basis, Root(RR!basis_free[i], field_exponent));
    end for;
    return real_basis;
end function;


/* embedding in RR of basis of extension */
Relative_real_basis_embedding := function(ground_field, extension, precision_float)
    ground_real_basis := [];
    ext_real_basis := [];
    ext_basis, ground_basis := Relative_primefree_basis(ground_field, extension);
    RR := RealField(precision_float);
    for i in [1..#ground_basis[1]] do
	Append(~ground_real_basis, Root(RR!ground_basis[1, i], ground_field[2]));
    end for;
    for i in [1..#ext_basis[1]] do
	Append(~ext_real_basis, Root(RR!ext_basis[1, i], extension[2]));
    end for;
    real_basis := [];
    return ext_real_basis, ground_real_basis;
end function;


KF_real_embedding := function(f, field_sequence, field_exponent, precision_float, basis_free:real_basis:=[])
    RR := RealField(precision_float);
    if #real_basis eq 0 then
	real_basis := KF_real_basis_embedding(basis_free, field_exponent, precision_float);
    end if;
    real_basis := ChangeRing(Vector(real_basis), RR);
    g := ChangeRing(Vector(f), RR);
    return InnerProduct(g, real_basis);
end function;


/* embedding in RR of f in a relative extension  */
Relative_real_embedding := function(f, ground_field, extension, precision_float:real_basis:=[])
    RR_plus := RealField(precision_float+#ground_field[1]+#extension[1]);
    RR := RealField(precision_float);
    if #real_basis eq 0 then
	a, b := Relative_real_basis_embedding(ground_field, extension, precision_float + #extension[1] + #ground_field[1]);
	real_basis := ElementToSequence(TensorProduct(Vector(a), Vector(b)));
    end if;
    real_basis := ChangeRing(Vector(real_basis), RR_plus);
    g := ChangeRing(Vector(f), RR_plus);
    return RR!InnerProduct(g, real_basis);
end function;


PartEmb_from_flat := function(g, list_pairs)
    h := [g[1]];
    for i in [1..#list_pairs] do
	Append(~h, g[list_pairs[i][1]]);
    end for;
    return h;
end function;


PartEmb_from_flat_family := function(G, list_pairs)
    H := [];
    for i in [1..#G] do
	Append(~H, PartEmb_from_flat(G[i], list_pairs));
    end for;
    return H;
end function;



PartLog_from_flat := function(g, list_pairs)
    h := [g[1]];
    for i in [1..#list_pairs] do
	Append(~h, 2*g[list_pairs[i][1]]);
    end for;
    return h;
end function;


PartLog_from_flat_family := function(G, list_pairs)
    H := [];
    for i in [1..#G] do
	Append(~H, PartLog_from_flat(G[i], list_pairs));
    end for;
    return H;
end function;




KF_complex_minkowski_embedding := function(f, field_sequence, field_exponent, precision_float: basis:=[], list_primes:=[], zeta_p:=1)
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    P<t> := PolynomialRing(IntegerRing());
    RR := RealField(precision_float+10+Round(Log(2, Norm(Vector(f))) /10));
    CC := ComplexField(precision_float+10+Round(Log(2, Norm(Vector(f)))/10));
    CC_res := ComplexField(precision_float+10);
    //"root of unity \n";
    if zeta_p eq 1 then
	zeta := CC!RootOfUnity(field_exponent);
    else
	zeta := zeta_p;
    end if;
    //"****************";
    //"roots of field sequence \n";
    Rpol<y> := PolynomialRing(CC, field_length);
    R := [[Root(RR!field_sequence[i], field_exponent)*zeta^(j-1) : j in [1..field_exponent]] : i in [1..field_length]];
    //"*****************";
    c := Vector_to_Polynomial(f, field_sequence, field_exponent, Rpol);
    //"******************";
    /* Rtest<X> := PolynomialRing(RealField(3)); */
    /* f, Rtest!c; */
    Mink := [CC!0 : i in [1..field_dim]];
    placed_list := [];
    mink := [];
    for i in [1..field_dim] do
	ind := Index(placed_list, i);
	if ind eq 0 then
	    e := Eltseq(ChangeRing(Vector(ChangeUniverse(IndexToExponent(i, field_length, field_exponent), GF(field_exponent))), IntegerRing()));
	    e_conj := [-e[j] mod field_exponent : j in [1..#e]];
	    i_conj := ExponentToIndex(e_conj, field_exponent);
	    List := [R[j, e[j]+1] : j in [1..field_length]];
	    m_e := CC!Evaluate(c, List);
	    Append(~mink, CC_res!m_e);
	    /* Mink[i] := m_e; */
	    /* Mink[i_conj] := CC!Conjugate(m_e); */
	    /* Append(~placed_list, i); */
	    /* Append(~placed_list, i_conj); */
	end if;
    end for;
    return mink, zeta;
end function;


KF_partial_complex_minkowski:= function(f, field_sequence, field_exponent, precision_float:
					basis:=[], list_primes:=[], depth:=1, zeta:=1, list_conj_pairs := [])
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    P<t> := PolynomialRing(IntegerRing());
    RR := RealField(precision_float+15);
    CC := ComplexField(precision_float+15);
    //"root of unity \n";
    if zeta eq 1 then
	zeta := CC!RootOfUnity(field_exponent);
    end if;
    //"****************";
    //"roots of field sequence \n";
    Rpol<y> := PolynomialRing(CC, field_length);
    R := [[Root(RR!field_sequence[i], field_exponent)*zeta^(j-1) : j in [1..field_exponent]] : i in [1..field_length]];
    //"*****************";
    c := Vector_to_Polynomial(f, field_sequence, field_exponent, Rpol);
    //"******************";
    /* Rtest<X> := PolynomialRing(RealField(3)); */
    /* f, Rtest!c; */
    V := VectorSpace(GF(field_exponent), depth);
    Mink := [];
    placed_list := [];
    list_pairs := list_conj_pairs;
    beta := ZeroSequence(Integers(), field_length-depth);
    if list_pairs eq [] then
	for v in V do
	    gamma := Eltseq(ChangeRing(v, Integers()));
	    gamma_conj := Eltseq(ChangeRing(-v, Integers()));
	    i_gamma := ExponentToIndex(gamma, field_exponent);
	    i_gamma_conj := ExponentToIndex(gamma_conj, field_exponent);
	    ind := Index(placed_list, i_gamma);
	    if ind eq 0 then
		e := beta cat gamma;
		List := [R[j, e[j]+1] : j in [1..field_length]];
		m_e := Evaluate(c, List);
		Append(~Mink, m_e);
		Append(~placed_list, i_gamma);
		Append(~placed_list, i_gamma_conj);
		if v ne V!0 then
		    Append(~list_pairs, [i_gamma, i_gamma_conj]);
		end if;
	    end if;
	end for;
    else
	gamma := ChangeUniverse(Eltseq(V!0), Integers());    
	e := beta cat gamma;
	List := [R[j, e[j]+1] : j in [1..field_length]];
	m_e := Evaluate(c, List);
	Append(~Mink, m_e);
	for i in [1..#list_pairs] do
	    gamma := IndexToExponent(list_pairs[i, 1], depth, field_exponent);
	    e := beta cat gamma;
	    List := [R[j, e[j]+1] : j in [1..field_length]];
	    m_e := Evaluate(c, List);
	    Append(~Mink, m_e);
	end for;
    end if;
    return Mink, zeta, list_pairs;
end function;


/* complete mink with the conjugates */
KF_complex_mink_from_half := function(half_mink, field_sequence, field_exponent, depth, list_index_pairs)
    /* RR := RealField(precision); */
    if field_exponent eq 2 then
	return half_mink;
    else 
	CC := Universe(half_mink);
	V := VectorSpace(GF(field_exponent), depth);
	list_placed := [];
	Mink := [CC!0 : i in [1..#half_mink*2-1]];
	Mink[1] := half_mink[1];
	Append(~list_placed, 1);
	/* readi jhbjbj; */
	list_ind_conj := list_index_pairs;
	count := 0;
	for i in [1..#list_index_pairs] do
	    Mink[list_index_pairs[i][1]] := half_mink[i+1];
	    Mink[list_index_pairs[i][2]] := Conjugate(half_mink[i+1]);	end for;
	return Mink;
    end if;
end function;


Relative_complex_minkowski := function(f, ground_field, extension, precision_float)
    r_ground := #ground_field[1];
    ground_dim := ground_field[2]^r_ground;
    r_ext := #extension[1];
    ext_dim := extension[2]^r_ext;
    P<t> := PolynomialRing(IntegerRing());
    /* define float fields */
    RR := RealField(precision_float+ext_dim+ground_dim);
    CC := ComplexField(precision_float+ext_dim+ground_dim);
    /* define needed roots of unity */
    zeta_ground := CC!RootOfUnity(ground_field[2]);
    zeta_ext := CC!RootOfUnity(extension[2]);
    Rpol := PolynomialRing(CC, r_ext+r_ground);
    /* complex embedding of basis of ground field */
    R_ground := [[Root(RR!ground_field[1,i], ground_field[2])*zeta_ground^(j-1) : j in [1..ground_field[2]]] : i in [1..r_ground]];
    /* complex embedding of basis of extension */
    R_ext := [[Root(RR!extension[1,i], extension[2])*zeta_ext^(j-1) : j in [1..extension[2]]] : i in [1..r_ext]];
    c := Relative_vector_to_polynomial(f, ground_field, extension, Rpol);
    Mink := [];
    for i in [1..ext_dim] do
	e_ext := ChangeRing(Vector(ChangeUniverse(IndexToExponent(i, r_ext, extension[2]), GF(extension[2]))), IntegerRing());
	list_ext := [R_ext[k, e_ext[k]+1] : k in [1..r_ext]];
	for j in [1..ground_dim] do
	    e_ground := ChangeRing(Vector(ChangeUniverse(IndexToExponent(j, r_ground, ground_field[2]), GF(ground_field[2]))), IntegerRing());
	    list_ground := [R_ground[l, e_ground[l]+1] : l in [1..r_ground]];
	    Append(~Mink, Evaluate(c, list_ground cat list_ext));
	end for;
    end for;
    return ChangeUniverse(Mink, ComplexField(precision_float));
end function;


Relative_partial_complex_minkowski:= function(f, ground_field, extension, precision_float: depth:=1, zeta:=1, list_conj_pairs := [])
    r_ground := #ground_field[1];
    ground_dim := ground_field[2]^r_ground;
    r_ext := #extension[1];
    ext_dim := extension[2]^r_ext;
    P<t> := PolynomialRing(IntegerRing());
    /* define float fields */
    RR := RealField(precision_float+ext_dim+ground_dim);
    CC := ComplexField(precision_float+ext_dim+ground_dim);
    /* define needed roots of unity */
    if zeta eq 1 then
	zeta_ext := CC!RootOfUnity(extension[2]);
    else
	zeta_ext := zeta;
    end if;
    Rpol := PolynomialRing(CC, r_ext+r_ground);
    /* complex embedding of basis of ground field */
    R_ground := [Root(RR!ground_field[1,i], ground_field[2]) : i in [1..r_ground]];
    /* complex embedding of basis of extension */
    R_ext := [[Root(RR!extension[1,i], extension[2])*zeta_ext^(j-1) : j in [1..extension[2]]] : i in [1..r_ext]];
    /* create pol corresponding to f */
    c := Relative_vector_to_polynomial(f, ground_field, extension, Rpol);
    Mink := [];
    placed_list := [];
    list_pairs := list_conj_pairs;
    alpha := ZeroSequence(Integers(), r_ground);
    beta := ZeroSequence(Integers(), r_ext-depth);
    list_ground := R_ground;
    if list_pairs eq [] then
	V := VectorSpace(GF(extension[2]), depth);
	for v in V do
            gamma := ElementToSequence(ChangeRing(v, Integers()));
	    gamma_conj := [-gamma[i] mod extension[2] : i in [1..depth]];
	    i_gamma := ExponentToIndex(gamma, extension[2]);
	    i_gamma_conj := ExponentToIndex(gamma_conj, extension[2]);
	    ind := Index(placed_list, i_gamma);
	    if ind eq 0 then
		e_ext := beta cat gamma;
		list_ext := [R_ext[k, e_ext[k]+1] : k in [1..r_ext]];
		Append(~Mink, Evaluate(c, list_ground cat list_ext));
		Append(~placed_list, i_gamma);
		Append(~placed_list, i_gamma_conj);
		if v ne V!0 then
		    Append(~list_pairs, [i_gamma, i_gamma_conj]);
		end if;
	    end if;
	end for;
    else
	gamma := ZeroSequence(Integers(), depth);
	e_ext := beta cat gamma;
	list_ext := [R_ext[k, e_ext[k]+1] : k in [1..r_ext]];
	Append(~Mink, Evaluate(c, list_ground cat list_ext));
	for i in [1..#list_pairs] do
    	    gamma := IndexToExponent(list_pairs[i, 1], depth, extension[2]);
	    e_ext := beta cat gamma;
	    list_ext := [R_ext[k, e_ext[k]+1] : k in [1..r_ext]];
	    Append(~Mink, Evaluate(c, list_ground cat list_ext));
	end for;
	
    end if;
    return Mink, zeta_ext, list_pairs;
end function;



KF_Log_embedding := function(f, field_sequence, field_exponent, precision: basis:=[], list_primes:=[])
    mink := KF_complex_minkowski_embedding(f, field_sequence, field_exponent, precision+10: basis:=[], list_primes:=[]);
    //"norm is ", &*mink;
    log := [];
    for i in [1..#mink] do
	Append(~log, Round(2^(precision)*Log(AbsoluteValue(mink[i])))/2^(precision));
    end for;
    return log;
end function;


Relative_Log_embedding := function(f, ground_field, extension, precision)
    mink := Relative_complex_minkowski(f, ground_field, extension, precision+30);
    //"norm is ", &*mink;
    log := [];
    for i in [1..#mink] do
	Append(~log, Round(2^(precision)*Log(AbsoluteValue(mink[i])))/2^(precision));
    end for;
    return log;
end function;


Coefficient_from_Minkowski := function(mink, index, real_basis_free, field_sequence, field_exponent, precision_float, zeta)
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    Coeff := 0;
    for j in [1..#mink] do
	beta := IndexToExponent(j, #field_sequence, field_exponent);
	t := Galois_action_index(beta, index, field_exponent);
	Coeff := Coeff + (zeta^((field_exponent-t) mod field_exponent))*mink[j];
    end for;
    return RationalField() ! (Round(Real(Coeff/(field_dim*real_basis_free[index]))));
end function;



Minkowski_to_vector := function(mink, basis_free, field_sequence, field_exponent, precision_float, zeta:real_free_basis :=[])
    if #real_free_basis ne 0 then
	real_basis := real_free_basis;
    else
	real_basis := KF_real_basis_embedding(basis_free, field_exponent, precision_float);
    end if;
    CC := ComplexField(precision_float);
    //zeta := CC!RootOfUnity(field_exponent);
    vector := [];
    for i in [1..#mink] do
	Append(~vector, Coefficient_from_Minkowski(mink, i, real_basis, field_sequence, field_exponent, precision_float, zeta));
    end for;
    return vector;
end function;


Complex_coefficient_from_minkowski := function(mink, index, real_basis_free, field_sequence, field_exponent, precision_float, zeta)
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    Coeff := 0;
    for j in [1..#mink] do
	beta := IndexToExponent(j, #field_sequence, field_exponent);
	t := Galois_action_index(beta, index, field_exponent);
	Coeff := Coeff + (zeta^((-t mod field_exponent)))*mink[j];
    end for;
    return (Coeff/(field_dim*real_basis_free[index]));
end function;


/* given relative minkowski embedding of x in K/L return the 
real embeddings of the coefficients of x over L 
CAREFUL : ONLY KUMMER SUPPORTED    */
Relative_complex_coefficient_from_minkowski := function(mink, index, ground_field, extension, precision_float, zeta: real_basis := [])
    field_dim := KF_dimension(extension);
    real_basis_free := real_basis;
    if real_basis_free eq [] then
	real_basis_free := Relative_real_basis_embedding(ground_field, extension, precision_float);
    end if;
    Coeff := 0;
    for j in [1..#mink] do
	beta := IndexToExponent(j, #extension[1], extension[2]);
	t := Galois_action_index(beta, index, extension[2]);
	Coeff := Coeff + (zeta^((extension[2]-t) mod extension[2]))*mink[j];
    end for;
    return (Coeff/(field_dim*real_basis_free[index]));
end function;


Complex_Minkowski_to_vector := function(mink, basis_free, field_sequence, field_exponent, precision_float, zeta:real_free_basis :=[])
    if #real_free_basis ne 0 then
	real_basis := real_free_basis;
    else
	real_basis := KF_real_basis_embedding(basis_free, field_exponent, precision_float);
    end if;
    CC := ComplexField(precision_float);
    vector := [];
    for i in [1..#mink] do
	Append(~vector, Complex_coefficient_from_minkowski(mink, i, real_basis, field_sequence, field_exponent, precision_float, CC!zeta));
    end for;
    return vector;
end function;


Relative_complex_minkowski_to_vector := function(mink, ground_field, extension, precision_float, zeta: real_basis:=[])
    real_basis_free := real_basis;
    if real_basis_free eq [] then
	real_basis_free := Relative_real_basis_embedding(ground_field, extension, precision_float);
    end if;
    vector := [];
    for i in [1..#mink] do
	Append(~vector, Relative_complex_coefficient_from_minkowski(mink, i, ground_field, extension, precision_float, zeta: real_basis:=real_basis_free));
    end for;
    return vector, real_basis_free;
end function;



KF_partial_mink := function(mink, field_sequence, field_exponent:depth:=1)
    rel_mink := [mink[1]];
    beta := ZeroSequence(IntegerRing(), #field_sequence);
    if field_exponent eq 2 then
	for i in [1..(field_exponent-1)] do
	    beta[#beta] := i;
	    index := ExponentToIndex(beta, field_exponent);
	    Append(~rel_mink, mink[index]);
	end for;
    else
	for i in [1..(field_exponent-1) div 2] do
	    beta[#beta] := i;
	    index := ExponentToIndex(beta, field_exponent);
	    Append(~rel_mink, mink[index]);
	end for;
    end if;
    return rel_mink;
end function;


Relative_partial_mink_from_power := function(mink, ground_field, extension, exponent, precision:depth:=1)
    RR := RealField(precision);
    CC<i> := ComplexField(precision);
    rel_mink := ZeroSequence(CC, extension[2]^depth);
    rel_mink[1] := CC!(Root(RR!(mink[1]), exponent));
    placed_indexes := [1];
    alpha := ZeroSequence(IntegerRing(), #ground_field[1]);
    beta := ZeroSequence(IntegerRing(), #extension[1]-depth);
    gamma := ZeroSequence(IntegerRing(), depth);
    V := VectorSpace(GF(extension[2]), depth);
    list_indexes_pair := [];
    for v in V do
	gamma := ElementToSequence(ChangeRing(v, Integers()));
	gamma_conj := [-gamma[i] mod extension[2] : i in [1..depth]];
	i_gamma := ExponentToIndex(gamma, extension[2]);
	i_gamma_conj := ExponentToIndex(gamma_conj, extension[2]);
	ind := Index(placed_indexes, i_gamma);
	if ind eq 0 then
	    sigma := [alpha, beta cat gamma];
	    index := Relative_exponent_to_index(sigma, ground_field, extension);
	    rel_mink[i_gamma] := CC!Root(CC!mink[index], exponent);
	    rel_mink[i_gamma_conj] := CC!Conjugate(rel_mink[i_gamma]);
	    if v ne V!0 then Append(~list_indexes_pair, [i_gamma, i_gamma_conj]); end if;
	    Append(~placed_indexes, i_gamma);
	    Append(~placed_indexes, i_gamma_conj);
	end if;
    end for;
    return rel_mink, list_indexes_pair;
end function;



KF_minim_from_mink := function(mink, precision_float, field_exponent)
    CC := ComplexField(precision_float);
    P<x> := PolynomialRing(CC);
    Minim := 1;
    for i in [1..#mink] do
	Minim := Minim*(x-CC!mink[i]);
    end for;
    Coeff := Coefficients(Minim);
    Coeff_test := [IsCoercible(IntegerRing(), Round((10^((precision_float div 2) + #mink))*Coeff[i])) : i in [1..#Coeff]];
    bool := &and Coeff_test;
    if (bool eq false) then
	return bool, Minim;
    else
	P1 := P![Round(Coeff[i]) : i in [1..#Coeff]];
	Test_irr := Factorization(P1)[1,1];
	return bool, Test_irr;
    end if;
end function;

KF_minim_from_vector := function(x, field_sequence, field_exponent, precision_float:mink:=[])
    if #mink eq 0 then
	Mink := KF_complex_minkowski_embedding(x, field_sequence, field_exponent, precision_float:basis:=[], list_primes:=[]);
    else
	Mink := mink;
    end if;
    bool, Test_irr := KF_minim_from_mink(mink, precision_float, field_exponent);
    while bool eq false do
	print "update of the precision";
	precision_float := Ceiling(precision_float*Sqrt(2));
	mink := KF_minim_from_mink(x, field_sequence, field_exponent, precision_float);
	bool, Test_irr := KF_minim_from_mink(mink, precision_float, field_exponent);
    end while;
    return Test_irr, precision_float, mink;
end function;

/* given minimal polynomial of x and minkowski embedding of x^p return minkowski embedding of x  */
KF_minkowski_from_power := function(mink_power, minim, field_exponent, precision_float)
    S<t> := PolynomialRing(IntegerRing());
    CC<i> := ComplexField(Ceiling(1.5*precision));
    zeta := CC!RootOfUnity(field_exponent);    
    Q<y> := PolynomialRing(CC);
    Mink := [];
    for i in [1..#(mink_power)] do
	s := Cputime();
	c := mink_power[i];
	r := Root(c, 3);
	R := [r*zeta^j : j in [0..field_exponent-1]];
	Eval_R := [Norm(Round(10^(precision_float div 2)*Evaluate(S!minim, R[i]))) : i in [1..#R]];
	m, j := Min(Eval_R);
	Append(~Mink, R[j]);
    end for;
    return Mink, zeta;
end function;


KF_complex_discriminant_pf := function(kummer_field, precision)
    field_sequence := kummer_field[1];
    field_exponent := kummer_field[2];
    field_dim := KF_dimension(kummer_field);
    M := [];
    CC := ComplexField(precision);
    zeta := CC!RootOfUnity(field_exponent);
    for i in [1..field_dim] do
	print i;
	a := ZeroSequence(Rationals(), field_dim);
	a[i] := 1;
	Append(~M, KF_complex_minkowski_embedding(a, field_sequence, field_exponent, precision:zeta_p:=zeta));
    end for;
    return Determinant(Matrix(M))^2;
end function;


KF_mink_exp := function(f, e,  kf, precision_float, basis_free: basis:=[], real_free_basis:=[])
    m_f, zeta := KF_complex_minkowski_embedding(f, kf[1], kf[2], precision_float+10: basis:=basis);
    m_f_e := seq_exp(m_f, e);
    return Complex_Minkowski_to_vector(m_f_e, basis_free, kf[1], kf[2], precision_float, zeta: real_free_basis:=real_free_basis);     
end function;

KF_mink_prod := function(f, g, kf, precision_float, basis_free: basis:=[], real_free_basis:=[])
    m_f, zeta := KF_complex_minkowski_embedding(f, kf[1], kf[2], precision_float+10: basis:=basis);
    m_g := KF_complex_minkowski_embedding(g, kf[1], kf[2], precision_float+10: basis:=basis, zeta_p:=zeta);
    m_h := Eltseq(Vector(m_g)*Vector(m_f));
    return Complex_Minkowski_to_vector(m_h, basis_free, kf[1], kf[2], precision_float, zeta: real_free_basis:=real_free_basis);     
end function;


KF_mink_exponentiation := function(list_elements, list_exp, kf, precision_float, basis_free
				   : basis:=[], real_free_basis:=[], KF:=RationalField())
    O_vec := [1] cat ZeroSequence(Rationals(), KF_dimension(kf)-1);
    m_x, zeta, list_pairs := KF_partial_complex_minkowski(O_vec, kf[1], kf[2], precision_float+10: basis:=basis, depth := #kf[1]);
    m_x := Vector(m_x);
    for i in [1..#list_elements] do
	if list_exp[i] ne 0 then
	    m_y :=  KF_partial_complex_minkowski(list_elements[i], kf[1], kf[2], precision_float+10: basis:=basis, depth := #kf[1], list_conj_pairs := list_pairs);
	    m_y := seq_exp(m_y, list_exp[i]);
	    m_x *:= Vector(m_y);
	end if;
    end for;
    m_x := KF_complex_mink_from_half(Eltseq(m_x), kf[1], kf[2], #kf[1], list_pairs);
    return Eltseq(Vector(Minkowski_to_vector(Eltseq(KF_dimension(kf)*Vector(m_x)), basis_free, kf[1], kf[2], precision_float, zeta:real_free_basis :=real_free_basis))/KF_dimension(kf));
end function;
