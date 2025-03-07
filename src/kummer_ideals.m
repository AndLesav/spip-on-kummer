/* test lattice has good determinant */
KF_subfield_lattice_test := function(Lat, subfield_sequence, field_sequence, field_exponent, determinant)
    Lat_test_basis := Subfield_lattice_intersection(Lat, subfield_sequence, field_sequence, field_exponent);
    if #Lat_test_basis ne 0 then
	if Nrows(Matrix(Lat_test_basis)) eq Ncols(Matrix(Lat_test_basis)) then
	    if AbsoluteValue(Determinant(Matrix(Lat_test_basis))) eq AbsoluteValue(determinant) then
		return true, [ElementToSequence(ChangeRing(Vector(Lat_test_basis[j]), Rationals())) : j in [1..#Lat_test_basis]];
	    end if;
	end if;
    end if;
    return false, [];
end function;

/* test lattice has good determinant -- relative version */
Relative_subfield_lattice_test := function(lat, ground_field, subextension, extension, determinant)
    Lat_test_basis := Relative_subfield_lattice_intersection(Lat, ground_field, subextension, extension);
    if #Lat_test_basis ne 0 then
	if AbsoluteValue(Determinant(Matrix(Lat_test_basis))) eq AbsoluteValue(determinant) then
	    return true, [ElementToSequence(ChangeRing(Vector(Lat_test_basis[j]), Rationals())) : j in [1..#Lat_test_basis]];
	end if;
    end if;
    return false, [];
end function;


/* ideal multiplication ; I is in K, J is in K(zeta_p) */
Ideal_multiplication_scalar := function(I, J, field_sequence, field_exponent:determinant:=0, intersection_lattice := [], subfield_sequence:=[])
    /* first product */
    H := Galois_closure_mult_scalar_family(I[1], J, field_sequence, field_exponent);
    H := HermiteForm(ChangeRing(Matrix(H), Integers()):Al:="Classical");
    H := RowSubmatrixRange(H, 1, Rank(H));

    if #intersection_lattice ne 0 then
	H1 := Lattice_intersection(H, ChangeRing(Matrix(intersection_lattice), Integers()));
    else
	H1 := H;
    end if;

    if (determinant ne 0) and (Rank(H1) ne 0) then   /*have good lattice already? */
	L := [ElementToSequence(H1[j]) : j in [1..Nrows(H1)]];
	t, Lat_test := KF_subfield_lattice_test(L, subfield_sequence, field_sequence, field_exponent, determinant);
	/* print t; */
	if t then
	    return t, Lat_test;
	end if;
    end if;

    for i in [2..#I] do

	X := Matrix(Galois_closure_mult_scalar_family(I[i], J, field_sequence, field_exponent));
	X := ChangeRing(X, Integers());
	//  s := Cputime();
	//    H;
	H := HNF_update_classical(H, X);
	H := ChangeRing(H, Integers());
	//    "update hnf in:", Cputime(s);
	if #intersection_lattice ne 0 then
	    H1 := Lattice_intersection(H, ChangeRing(Matrix(intersection_lattice), Integers()));
	else H1 := H;
	end if;
	if (determinant ne 0) and (Rank(H1) ne 0) then   /*have good lattice already? */
	    L := [ElementToSequence(H1[j]) : j in [1..Nrows(H1)]];
	    t, Lat_test := KF_subfield_lattice_test(L, subfield_sequence, field_sequence, field_exponent, determinant);
	    if t then
		return t, Lat_test;
	    end if;
	end if;
	X := Matrix(Galois_closure_mult_scalar_family(I[i], J, field_sequence, field_exponent));
	H := HNF_update_classical(H, X);
    end for;
    return false, [ElementToSequence(H[i]) : i in [1..Nrows(H)]]; 
end function;



/* ideal multiplication ; I is in K, J is in K(zeta_p) -- relative version */
Relative_ideal_multiplication_scalar := function(I, J, ground_field, extension: determinant:=0, intersection_lattice := [], subextension := <>)
    H := Relative_galois_closure_mult_scalar_family(I[1], J, ground_field, extension);
    H := HermiteForm(ChangeRing(Matrix(H), Integers()):Al:="Classical");
    if #intersection_lattice ne 0 then
	H := Lattice_intersection(H, ChangeRing(Matrix(intersection_lattice), Integers()));
	/* H := BasisMatrix(Lattice(H) meet Lattice(ChangeRing(Matrix(intersection_lattice), Integers()))); */
    end if;
    for i in [2..#I] do
	if (determinant ne 0) and (#subextension ne 0) and (Rank(H) ne 0) then
	    L := [ElementToSequence(H[j]) : j in [1..Nrows(H)]];
	    t, Lat_test := Relative_subfield_lattice_test(L, ground_field, subextension, extension, determinant);
	    if t then
		return t, Lat_test;
	    end if;
	end if;    
	X := Matrix(Relative_galois_closure_mult_scalar_family(I[i], J, ground_field, extension));
	s := Cputime();
	H := HNF_update_classical(H, X);
	//"update hnf in:", Cputime(s);
    end for;
    if (determinant ne 0) and (#subextension eq 0) then
	L := [ElementToSequence(H[j]) : j in [1..Nrows(H)]];
	t, Lat_test := Relative_subfield_lattice_test(L, ground_field, subextension, extension, determinant);
	if t then
	    return t, Lat_test;
	end if;
    end if;
    return false, [ElementToSequence(H[i]) : i in [1..Nrows(H)]]; 
end function;



/* ideal multiplication ; I is in K, J is in K(zeta_p)*/
Ideal_multiplication_galois := function(I, J, field_sequence, field_exponent:determinant:=0)
    H := Galois_closure_multiplication_family(I[1], J, field_sequence, field_exponent);
    H := HermiteForm(ChangeRing(Matrix(H), Integers()):Al:="Classical");
    for i in [2..#I] do
	X := Matrix(Galois_closure_multiplication_family(I[i], J, field_sequence, field_exponent));
	s := Cputime();
	H := HNF_update_classical(H, X);
    end for;
    return [ElementToSequence(H[i]) : i in [1..Nrows(H)]]; 
end function;


/* ideal multiplication test */
Ideal_multiplication_test := function(I, J, field_sequence, field_exponent)
    M := Matrix(I);
    N := Matrix(J);
    print "**********************************";
    Inter := (Lattice(M) meet Lattice(N));
    dM := Denominator(M);
    dN := Denominator(N);
    d := LCM(dM, dN);
    M := HermiteForm(ChangeRing(d*M, Integers()));
    N := HermiteForm(ChangeRing(d*N, Integers()));
    H := ChangeRing(HNF_update_classical(M, N), Rationals())/d ;
    H1 := LLL(H);
    H := [ElementToSequence(H[i]) : i in [1..Nrows(H)]];
    H := Ideal_multiplication_galois(H1, H, field_sequence, field_exponent);
    A := Lattice(Matrix(H)) meet Inter;
    A := ChangeRing(BasisMatrix(A), Rationals());
    return [ElementToSequence(A[i]) : i in [1..Nrows(A)]];
end function;


/* intersection of all sigma^i(I) */
KF_ideal_cyclic_intersection := function(I, field_sequence, subfield_sequence, beta, field_exponent:determinant:=0) 
    J := Galois_morphism_closure_family(I, beta, field_sequence, field_exponent);
    I1 := HorizontalJoin(Matrix(I), ZeroMatrix(Rationals(), field_exponent^#field_sequence, (field_exponent-2)*field_exponent^#field_sequence));
    J := Lattice(I1) meet Lattice(Matrix(J));
    J := BasisMatrix(J);
    J := [ElementToSequence(J[i]) : i in [1..Rank(J)]];
    for j in [1..field_exponent-2] do
	//	j;
	J := Galois_morphism_closure_family(J, beta, field_sequence, field_exponent);
	J := Lattice(Matrix(I1)) meet Lattice(Matrix(J));
	J := BasisMatrix(J);
	J := [ElementToSequence(J[i]) : i in [1..Rank(J)]];
    end for;
    return J;
end function;


/* intersection of all sigma^i(I) -- relative version */
Relative_ideal_cyclic_intersection := function(I, beta, ground_field, extension:determinant:=0)
    field_dim := Relative_extension_dimension(ground_field, extension)[1];
    J := Relative_galois_closure_morphism_family(I, beta, ground_field, extension);
    I1 := HorizontalJoin(Matrix(I), ZeroMatrix(Rationals(), field_dim, ((ground_field[2]-1)*(extension[2]-1)-1)*field_dim));
    J := Lattice(I1) meet Lattice(Matrix(J));
    J := BasisMatrix(J);
    J := [ElementToSequence(J[i]) : i in [1..Rank(J)]];
    for j in [1..extension[2]-2] do
	J := Relative_galois_closure_morphism_family(J, beta, ground_field, extension);
	J := Lattice(Matrix(I1)) meet Lattice(Matrix(J));
	J := BasisMatrix(J);
	J := [ElementToSequence(J[i]) : i in [1..Rank(J)]];
    end for;
    return J;
end function;


/* Ideal_norm with respect to one complex embedding beta */
KF_ideal_relative_norm := function(I, field_sequence, subfield_sequence, beta, field_exponent:determinant:=0, rep:="two_el", method:="naive")
    if determinant eq 0 then
	determinant := Determinant(Matrix(I));
    end if;
    if method eq "inter" then     
	L_meet := KF_ideal_cyclic_intersection(I, field_sequence, subfield_sequence, beta, field_exponent);
	print "intersection computed";
	if determinant ne 0 then
	    t, Lat_test_basis := KF_subfield_lattice_test(L_meet, subfield_sequence, field_sequence, field_exponent, determinant);
	    if t then
		print "ideal norm found after inter"; 
		return Lat_test_basis, 0;
	    else
		return false, 100;
	    end if;
	end if;
    end if;
    J := I;
    if rep eq "two_el" then
	I := Kummer_Ideal_two_elements(I, <field_sequence, field_exponent>);
    else
	I := LLL(Matrix(I));
	I := [ElementToSequence(I[i]) : i in [1..Nrows(I)]];
    end if;

    J := Galois_morphism_closure_family(J, beta, field_sequence, field_exponent);

    if method eq "naive" then
	t, J := Ideal_multiplication_scalar(I, J, field_sequence, field_exponent:/* determinant:=determinant *//* , intersection_lattice := L_meet, */ subfield_sequence := subfield_sequence);
    elif method eq "det" then
	t, J := Ideal_multiplication_scalar(I, J, field_sequence, field_exponent:determinant:=determinant, /* , intersection_lattice := L_meet */ subfield_sequence := subfield_sequence);
    elif method eq "inter" then
	t, J := Ideal_multiplication_scalar(I, J, field_sequence, field_exponent:determinant:=determinant, intersection_lattice := L_meet, subfield_sequence := subfield_sequence);
    end if;

    print Rank(Matrix(J));
    if t then
	print "ideal norm found in step ", 1, " for rep ", rep; 
	return J, 1;
    end if;

    for i in [2..field_exponent-1] do
	print i;
	J := Galois_morphism_closure_family(J, beta, field_sequence, field_exponent);

	/* print "before multiplication"; */
	if method eq "naive" then
	    t, J := Ideal_multiplication_scalar(I, J, field_sequence, field_exponent:/* determinant:=determinant *//* , intersection_lattice := L_meet, */ subfield_sequence := subfield_sequence);
	elif method eq "det" then
	    t, J := Ideal_multiplication_scalar(I, J, field_sequence, field_exponent: determinant:=determinant, /* , intersection_lattice := L_meet */ subfield_sequence := subfield_sequence);
	/* print t; */
	elif method eq "inter" then
	    t, J := Ideal_multiplication_scalar(I, J, field_sequence, field_exponent: determinant:=determinant, intersection_lattice:=L_meet, subfield_sequence:=subfield_sequence);
	end if;

	if t then
	    print "ideal norm found in step ", i, " for rep ", rep; 
	    return J, i;
	end if;

    end for;
    Lat_test_basis := Subfield_lattice_intersection(J, subfield_sequence, field_sequence, field_exponent);
    return [ElementToSequence(ChangeRing(Vector(Lat_test_basis[j]), Rationals())) : j in [1..#Lat_test_basis]];
end function;


/* Ideal norm with respect to one complex embedding beta  -- relative version */
Relative_ideal_relative_norm := function(I, beta, ground_field, subextension, extension: determinant:=0)
    L_meet := Relative_ideal_cyclic_intersection(I, beta, ground_field, extension: determinant:=determinant);
    if determinant ne 0 then
	t, Lat_test_basis := Relative_subfield_lattice_test(L_meet, ground_field, subextension, extension, determinant);
	if t then
	    return Lat_test_basis;
	end if;
    end if;
    I := LLL(Matrix(I));
    I := [ElementToSequence(I[i]) : i in [1..Nrows(I)]];
    J := Relative_galois_closure_morphism_family(I, beta, ground_field, extension);
    t, J := Relative_ideal_multiplication_scalar(I, J, ground_field, extension: /* determinant:=determinant, */  intersection_lattice := L_meet, subextension := subextension);
    if t then
	return J;
    end if;
    for i in [1..extension[2]-2] do
	J := Relative_galois_closure_morphism_family(J, beta, ground_field, extension);
	t, J := Relative_ideal_multiplication_scalar(I, J, ground_field, extension: determinant:=determinant, intersection_lattice := L_meet, subextension := subextension);
	"denom is", Denominator(Matrix(J));
	if t then
	    return J;
	end if;
    end for;
    Lat_test_basis := Relative_subfield_lattice_intersection(J, ground_field, subextension, extension);

    return [ElementToSequence(ChangeRing(Vector(Lat_test_basis[j]), Rationals())) : j in [1..#Lat_test_basis]];
end function;



/* relative ideal norm with respect to embeddings <sigman_{depth+1}, ..., sigma_n>  */
KF_ideal_relative_norm_tower := function(I, field_sequence, field_exponent, depth)
    J := I;
    det := Determinant(Matrix(J));
    seq := field_sequence;
    for i in [1..depth] do
	sub_seq := Prune(seq);
	beta := ZeroSequence(Integers(), #seq);
	beta[#beta] := 1;
	J := KF_ideal_relative_norm(J, seq, sub_seq, beta, field_exponent:determinant:=det);
	J;
	seq := sub_seq;
    end for;
    return J;
end function;



/* creation of relative norm of ideals needed in computation */
KF_ideal_norm_list := function(g, field_sequence, field_exponent:Ideal_norms_list := [* [* *], [* *] *])
    Ideal_norms_list := Ideal_norms_list;
    if #field_sequence eq 1 then
	/* index := Index(Ideal_norms_list, [ground_field, extension]); */
	/* if index eq 0 then */
	/* 	ideal := Relative_IntegralBasis_creation(g, ground_field, extension); */
	/* 	Append(~Ideal_norms_list[1], [ground_field, extension]); */
	/* 	Append(~Ideal_norms_list[2], ideal); */
	/* end if; */
	return Ideal_norms_list;
    else
	n := #field_sequence;
	ms := field_sequence[n-1];
	mt := field_sequence[n];
	m_0 := Prune(Prune(field_sequence));
	beta := ZeroSequence(Integers(), n);
	field_basis := KF_primefree_basis(field_sequence, field_exponent);

	for i := 0 to (field_exponent-1) do
	    /* define morphism beta which is sigma_(n-1)sigma_n^i */
	    beta[n-1] := 1;			
	    beta[n] := i;

	    /* define subextension = K^beta */
	    subfield_sequence := m_0 cat [ms^(-i mod field_exponent)*mt];
	    subfield_basis := KF_primefree_basis(subfield_sequence, field_exponent);
	    g_norm := KF_norm_morphism_simple(g, beta, field_sequence, field_exponent);
	    g_norm := KF_subfield_embedding(g_norm, subfield_basis, field_basis, field_exponent);
	    index := Index(Ideal_norms_list, field_sequence);
	    if index eq 0 then
		ideal := KF_IntegralBasis_creation(g_norm, subfield_sequence, field_exponent);
		Append(~Ideal_norms_list[1], subfield_sequence);
		Append(~Ideal_norms_list[2], ideal);
	    end if;
	    Ideal_norms_list := $$(g_norm, subfield_sequence, field_exponent:Ideal_norms_list:=Ideal_norms_list);
	end for;

	/* define morphism beta which is sigma_(n-1)sigma_n^i */
	beta[n-1] := 0;			
	beta[n] := 1;

	/* define subextension = K^beta */
	subfield_sequence := m_0 cat [ms];
	subfield_basis := KF_primefree_basis(subfield_sequence, field_exponent);
	index := Index(Ideal_norms_list, subfield_sequence);
	g_norm := KF_norm_morphism_simple(g, beta, field_sequence, field_exponent);
	g_norm := KF_subfield_embedding(g_norm, subfield_basis, field_basis, field_exponent);
	if index eq 0 then
	    ideal := KF_IntegralBasis_creation(g_norm, subfield_sequence, field_exponent);
	    Append(~Ideal_norms_list[1], subfield_sequence);
	    Append(~Ideal_norms_list[2], ideal);
	end if;
	Ideal_norms_list := $$(g_norm, subfield_sequence, field_exponent:Ideal_norms_list:=Ideal_norms_list);
    end if;
    return Ideal_norms_list;
end function;    



/* 
 * Creation of relative norm of ideals needed in computation.
 * Ideal `I` is assumed to be given as a sequence of 1 or 2 elements.
*/
KF_ideal_norm_list_magma := function (I, field_sequence, field_exponent : Ideal_norms_list := [* [* *], [* *] *])
    ZZ<x> := PolynomialRing(Integers());
    
    /* Kummer field structure */
    kf := <field_sequence, field_exponent>;
    
    Ideal_norms_list := Ideal_norms_list;

    if #field_sequence eq 1 then
	return Ideal_norms_list;
    else
	n := #field_sequence;
	ms := field_sequence[n-1];
	mt := field_sequence[n];
	m_0 := Prune(Prune(field_sequence));
	sigma := ZeroSequence(Integers(), n);
	field_basis := KF_primefree_basis(field_sequence, field_exponent);


	/* Compute 2 elts rep of ideal if `I` is given by 1 element only */
	if #I eq 1 then
	    ideal := KF_IntegralBasis_creation(I[1], field_sequence, field_exponent);
	    ideal := Kummer_Ideal_two_elements(ideal, kf);
	else
	    ideal := I;
	end if;
	
	for i := 0 to (field_exponent-1) do
	    print i+1, " th subfield";
	    /* define morphism beta which is sigma_(n-1)sigma_n^i */
	    sigma[n-1] := 1;
	    sigma[n] := i;
	    
	    /* define subextension = K^beta */
	    subfield_sequence := m_0 cat [ms^(-i mod field_exponent)*mt];
	    subfield_basis := KF_primefree_basis(subfield_sequence, field_exponent);
	    
	    index := Index(Ideal_norms_list, field_sequence);

	    if index eq 0 then
		
		/* creation of necessary structures  */
		kf_sub := <subfield_sequence, field_exponent>;
		kf_new := <subfield_sequence cat [kf[1][#kf[1]-1]], kf[2]>;
		K := KF_creation(kf_sub[1], kf_sub[2]);
		L := ext<K | x^kf[2]-kf[1][#kf[1]-1]>;
		K1 := AbsoluteField(K);
		
		OL := MaximalOrder(L); /* assume L is not too large */
		OK := MaximalOrder(K1);
		q<y> := PolynomialRing(OK);
		
		ideal_tmp := [KF_coord_perm_elt(_j, kf_new, kf) : _j in ideal];
		ideal_tmp := [Vector_to_NFelement1(_g, kf_new[1], kf[2]: KF:=L) : _g in ideal_tmp];

		J := ideal < OL | ideal_tmp >;
		J := Norm(J);

		alpha, beta := TwoElement(J);

		
		
		Append(~Ideal_norms_list[1], subfield_sequence);
		Append(~Ideal_norms_list[2], [NFelement_to_vector1(K!alpha, kf_sub[1], kf_sub[2]), NFelement_to_vector1(K!beta, kf_sub[1], kf_sub[2])]);
	    end if;

	    Ideal_norms_list := $$([K!alpha, K!beta], subfield_sequence, field_exponent:Ideal_norms_list:=Ideal_norms_list);
	end for;

	/* define morphism beta which is sigma_(n-1)sigma_n^i */
	sigma[n-1] := 0;
	sigma[n] := 1;


	
	/* define subextension = K^beta */
	subfield_sequence := m_0 cat [ms];
	subfield_basis := KF_primefree_basis(subfield_sequence, field_exponent);
	index := Index(Ideal_norms_list, subfield_sequence);

	if index eq 0 then
	    
	    /* creation of necessary structures  */
	    kf_sub := <subfield_sequence, field_exponent>;
	    kf_new := <subfield_sequence cat [kf[1][#kf[1]]], kf[2]>;
	    
	    K := KF_creation(kf_sub[1], kf_sub[2]);
	    L := ext<K | x^kf[2]-kf[1][#kf[1]]>;
	    K1 := AbsoluteField(K);
	    
	    OL := MaximalOrder(L); /* assume L is not too large */
	    OK := MaximalOrder(K1);
	    q<y> := PolynomialRing(OK);
	    
	    ideal_tmp := [KF_coord_perm_elt(_j, kf_new, kf) : _j in ideal];
	    ideal_tmp := [Vector_to_NFelement1(_g, kf_new[1], kf[2]: KF:=L) : _g in ideal_tmp];
	    J := ideal < OL | ideal_tmp >;
	    J := Norm(J);
	    alpha, beta := TwoElement(J);
	    
	    
	    
	    Append(~Ideal_norms_list[1], subfield_sequence);
	    Append(~Ideal_norms_list[2], [NFelement_to_vector1(K!alpha, kf_sub[1], kf_sub[2]), NFelement_to_vector1(K!beta, kf_sub[1], kf_sub[2])]);
	end if;

	    Ideal_norms_list := $$([K!alpha, K!beta], subfield_sequence, field_exponent:Ideal_norms_list:=Ideal_norms_list);

    end if;
    
    return Ideal_norms_list;
end function;




/* creation of relative norm of ideals needed in computation */
/* /!\ this is related to kummer ext. with one exponent */
Relative_ideal_norm_list := function(g, ground_field, extension:Ideal_norms_list := [* [* *], [* *] *])
    Ideal_norms_list := Ideal_norms_list;
    a := KF_is_simple(ground_field);
    b := KF_is_simple(extension);
    if (a and b) then
	return Ideal_norms_list;
    elif (b and (not a)) then
	ground1 := extension;
	ext1 := ground_field;
	g1 := Relative_swap_field_rep(g, ground_field, extension);
	Ideal_norms_list := $$(g1, ground1, ext1:Ideal_norms_list:=Ideal_norms_list);
	return Ideal_norms_list;
    elif (not b) then
	ms := extension[1][#extension[1]-1];
	mt := extension[1][#extension[1]];
	m_0 := Prune(Prune(extension[1]));
	beta_ground := ZeroSequence(Integers(), #ground_field[1]);
	beta_ext := ZeroSequence(Integers(), #extension[1]);
	for i := 0 to (extension[2]-1) do
	    /* **** define morphism beta which is sigma_(n-1)sigma_n^i  **** */
	    beta_ext[#extension[1]-1] := 1;			
	    beta_ext[#extension[1]] := i;
	    beta := [beta_ground, beta_ext];
	    /* **** define subextension = Inv(beta) **** */
	    subextension := <m_0 cat [ms^(-i mod extension[2])*mt], extension[2]>;
	    g_norm := Relative_subfield_embedding(Relative_norm_morphism_simple(g, beta, ground_field, extension), ground_field, subextension, extension);
	    index := Index(Ideal_norms_list, [ground_field, subextension]);
	    if index eq 0 then
		ideal := Relative_IntegralBasis_creation(g_norm, ground_field, subextension);
		Append(~Ideal_norms_list[1], [ground_field, subextension]);
		Append(~Ideal_norms_list[2], ideal);
	    end if;
	    Ideal_norms_list := $$(g_norm, ground_field, subextension:Ideal_norms_list:=Ideal_norms_list);
	end for;
	/* define morphism beta which is sigma_(n-1)sigma_n^i */
	beta_ext[#extension[1]-1] := 0;			
	beta_ext[#extension[1]] := 1;
	beta := [beta_ground, beta_ext];
	/* define subextension = Inv(beta) */
	subextension := <m_0 cat [ms], extension[2]>;
	index := Index(Ideal_norms_list, [ground_field, subextension]);
	g_norm := Relative_subfield_embedding(Relative_norm_morphism_simple(g, beta, ground_field, extension), ground_field, subextension, extension);
	if index eq 0 then	
	    ideal := Relative_IntegralBasis_creation(g_norm, ground_field, subextension);
	    Append(~Ideal_norms_list[1], [ground_field, subextension]);
	    Append(~Ideal_norms_list[2], ideal);
	end if;
	Ideal_norms_list := $$(g_norm, ground_field, subextension:Ideal_norms_list:=Ideal_norms_list);
    end if;
    return Ideal_norms_list;
end function;    


/* Reduction of g in Log-unit Lattice U */
KF_RedGen := function(g, U, field_sequence, field_exponent: red_method:="babai")
    d:=field_sequence;    
    Mu := [U[i, 2] : i in [1..#U]];
    Mu := Matrix(Mu);
    g2 := g[2];
    ONE := [Rationals()!1 : i in [1..#g2]];
    g3 := Orthogonal_projection(g2, ONE);
    T := Cputime();
    if red_method eq "babai" then
	g_red_2, relations := Babai_decoding(Mu, g2);
    elif red_method eq "cvp" then
	Lu := Lattice(Mu);
	CV := ClosestVectors(Lu, Vector(g3))[1];
	d := Denominator(Mu);
	relations := ChangeUniverse(ElementToSequence(-Solution(ChangeRing(d*Mu, Integers()), ChangeRing(d*CV, Integers()))), Integers()) cat [1];
	g_red_2 := ElementToSequence(Vector(g2) - CV);
    else
	print "ERROR: WRONG METHOD NAME GIVEN";
	return false;
	exit;
    end if;
    t_decod := Cputime(T);
    T := Cputime();
    K := KF_creation(field_sequence, field_exponent);
    U1 := [U[i,1] : i in [1..#U]];
    g_red_1 := KF_exponentiation(U1 cat [g[1]], relations, field_sequence, field_exponent);
    t_recons := Cputime(T);
    return [g_red_1, g_red_2], t_decod, t_recons;
end function;


// Reduction of g in Log-unit Lattice U -- relative version
Relative_reduction_generator := function(g, U, ground_field, extension: red_method:="babai")
    print "starting reduction";    
    Mu := [U[i, 2] : i in [1..#U]];
    Mu := Matrix(Mu);
    g2 := g[2];
    ONE := [Rationals()!1 : i in [1..#g2]];
    g3 := Orthogonal_projection(g2, ONE);
    T := Cputime();
    if red_method eq "cvp" then
	Lu := Lattice(Mu);
	CV := ClosestVectors(Lu, Vector(g3))[1];
	relations := ChangeUniverse(ElementToSequence(Solution(Mu, ChangeRing(CV, RationalField()))), IntegerRing());
	g_red_2 := ElementToSequence(Vector(g2) - CV);
    elif red_method eq "babai" then
	g_red_2, relations := Babai_decoding(Mu, g3);
    else
	print "ERROR: WRONG METHOD NAME GIVEN";
	return false;
	exit;
    end if;
    t_decod := Cputime(T);
    T:=Cputime();
    K := Relative_extension_creation(ground_field, extension);
    U1 := [U[i,1] : i in [1..#U]];
    g_red_1 := Relative_exponentiation(U1 cat [g[1]], relations, ground_field, extension);
    t_recons := Cputime(T);
    return [g_red_1, g_red_2], t_decod, t_recons;
end function;


/* compute generator of ideal given a generator of the power of the ideal */
KF_Ideal_Gen_From_power := function(h, field_sequence, field_exponent, precision_log, U, basis_free: Units_List := [* [* *], [* *] *], precision := 1, lattice := Real_basis_lattice_init(basis_free, field_sequence, field_exponent), uni := IdentityMatrix(RationalField(), field_exponent^#field_sequence), bool := false)
    s := Cputime();
    if #U eq 0 then
	U, Units_List, precision, lattice, uni := KF_units_real(field_sequence, field_exponent, precision_log, bool: Units_List := Units_List);
    end if;
    Tunits := Cputime(s);

    A := [U[i, 1] : i in [1..#U]];
    B := [U[i, 2] : i in [1..#U]];
    field_dim := field_exponent^#field_sequence;
    Uone := [-1] cat ZeroSequence(Rationals(), field_dim-1);
    Append(~A, Uone);
    Append(~B, ZeroSequence(Rationals(), field_dim));
    M := Transpose(EnoughCharacters(Append(A, h[1]), field_sequence, field_exponent));
    H := M[Nrows(M)];
    RemoveRow(~M, Nrows(M));

    /* just before solving linear system" */
    f := ChangeRing(Solution(M, (field_exponent-1)*H), IntegerRing());
    s := Cputime();
    K := KF_creation(field_sequence, field_exponent);
    Pow := [NFelement_to_vector1(&*[ Vector_to_NFelement1(A[i], field_sequence, field_exponent: KF:=K)^f[i] : i in [1..(#A)]]*Vector_to_NFelement1(h[1], field_sequence, field_exponent: KF:=K), field_sequence, field_exponent)][1];
    depth := KF_depth(<field_sequence, field_exponent>);
    if precision eq 1 then bool := false; end if;
    print "precision before root in gen_from_power: ", precision;
    /* computing roots */
    if depth eq 0 then
	g1, precision, lattice, uni := Real_root_family([ChangeUniverse(Pow, Rationals())], field_sequence, field_exponent, basis_free: precision:=precision, lattice:=lattice, unitary := uni, bool := bool);
    else
	g1, precision, lattice, uni := Real_root_family_depth([ChangeUniverse(Pow, Rationals())], field_sequence, field_exponent, basis_free: precision:=precision, lattice:=lattice, unitary := uni, bool := bool, depth:=depth);
    end if;
    g1 := g1[1];
    g2 := ElementToSequence(ChangeRing((&+ [Vector(B[i])*f[i]/field_exponent : i in [1..#A]]), RationalField()) + ChangeRing(Vector(h[2])/field_exponent, RationalField()));
    print "the time to compute the final root is for the field defined by", field_sequence, "is", Cputime(s);
    return [g1, g2], precision, lattice, uni;
end function;


/* compute generator of ideal given a generator of the power of the ideal */
Relative_Ideal_Gen_From_power := function(h, ground_field, extension, precision_log,
					  U: Units_list := [* [* *], [* *] *],
					     depth:=1, precision:=1, basis_lattice:=1,
					     unitary:=1)
    sub_ext := <extension[1][1..#extension[1]-depth], extension[2]>;
    /* computes units if not already */
    /* initialise lattice if not given */
    if precision ne 1 then
	lattice := basis_lattice;
	prec := precision;
	uni := unitary;
    else
	lattice, uni := Relative_real_basis_lattice_init(ground_field, sub_ext);
	precicsion := 1;
    end if;
    index := Index(Units_list[1], [ground_field, extension]);
    s := Cputime();
    if (index ne 0) and (#U eq 0) then
	U := Units_list[2, index];
    elif (index eq 0) and (#U eq 0) then
	U, Units_list, precision, lattice, uni := Relative_units_real(ground_field, extension, precision_log: Units_list := Units_list);
    end if;
    /* print "units of the field defined by", field_sequence, "computed in", Cputime(s); */
    Tunits := Cputime(s);
    A := [U[i, 1] : i in [1..#U]];
    field_dim := Relative_extension_dimension(ground_field, extension)[1];
    Uone := [-1] cat ZeroSequence(Rationals(), field_dim-1);
    Append(~A, Uone);
    B := [U[i, 2] : i in [1..#U]];
    Append(~B, ZeroSequence(Rationals(), field_dim));
    /* detect power */
    M := Transpose(Relative_EnoughCharacters(Append(A, h[1]), ground_field, extension));
    H := M[Nrows(M)];
    RemoveRow(~M, Nrows(M));
    print "just before solving linear system";

    /* solve system */
    f := ChangeRing(Solution(M, (extension[2]-1)*H), IntegerRing());
    print "solution found, going to compute its root";
    s := Cputime();
    K := Relative_extension_creation(ground_field, extension);
    /* compute power */
    Pow := Relative_NFelement_to_vector1((&*[ Relative_vector_to_NFelement1(A[i], ground_field, extension: KE:=K)^f[i] : i in [1..(#A)]])*Relative_vector_to_NFelement1(h[1], ground_field, extension: KE:=K), ground_field, extension);
    /* compute root */
    a, d_t := Relative_depth(ground_field, extension);
    depth := d_t;
    if a eq 1 then
	g1, precision, lattice, uni := Relative_real_root_family_depth([Pow], ground_field, extension, extension[2]: depth:=depth, precision:=precision, basis_lattice:=lattice, unitary:=uni);
    elif a eq 0 then
	Pow_s := Relative_swap_field_rep_family([Pow], ground_field, extension)[1];
	g1, precision, lattice, uni := Relative_real_root_family_depth([Pow_s], extension, ground_field, extension[2]: depth:=depth, precision:=precision, basis_lattice:=lattice, unitary:=uni);
	g1 := Relative_swap_field_rep_family(g1, extension, ground_field);
    end if;
    /* put it together */
    g1 := g1[1];
    g2 := ElementToSequence(ChangeRing((&+ [Vector(B[i])*f[i]/extension[2] : i in [1..#A]]), RationalField()) + ChangeRing(Vector(h[2])/extension[2], RationalField()));
    return [g1,g2], U, precision, lattice, uni;
end function;


KF_PIP_integralbasis := function(I, field_sequence, field_exponent, basis_free, precision_log, U: Units_List := [* [* *], [* *] *], Norms_List := [* [* *],  [* *] *], precision := 1, lattice := Real_basis_lattice_init(basis_free, field_sequence, field_exponent), uni := IdentityMatrix(Rationals(), field_exponent^#field_sequence), bool := false, norms_bool := false, red_method:="babai")
    Units_List1 := Units_List;
    if U eq [] then
	index := Index(Units_List1[1], field_sequence);
	if index ne 0 then
	    U := Units_List1[2, index];
	    print "units given";
	else
	    U := KF_units_real(field_sequence, field_exponent, precision_log, false);
	    Append(~Units_List1[1], field_sequence);
	    Append(~Units_List1[2], U);
	    print "units computed";
	end if;
    end if;
    print "After units";
    n := #field_sequence;
    field_dim := field_exponent^n;
    p<x> := PolynomialRing(RationalField());
    if (n eq 0) then
	return [];
    elif (n eq 1) then
	K := KF_creation(field_sequence, field_exponent);  // creation of MCF(d)
	O := (MaximalOrder(K));
	J := [Vector_to_NFelement1(I[i], field_sequence, field_exponent:KF:=K) : i in [1..#I]];
	t, g := IsPrincipal(ideal<O | J>);
	h1 := NFelement_to_vector1((K ! g), field_sequence, field_exponent);
	h2 := KF_Log_embedding(h1, field_sequence, field_exponent, precision_log);
	return [h1, h2];
    else
	print "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
	m_0 := field_sequence[1..n-2];
	ms := field_sequence[n-1];
	mt := field_sequence[n];
	beta := ZeroSequence(Integers(), n);
	g := [ZeroSequence(Rationals(), field_dim), ZeroSequence(Rationals(), field_dim)];
	g[1,1] := 1;
	field_basis_free := KF_primefree_basis(field_sequence, field_exponent);
	t_norm := 0;
	/* start recursive process */
	for i := 0 to (field_exponent-1) do
	    beta[n-1] := 1;			/* beta is sigma_(n-1)sigma_n^i */
	    beta[n] := i;
	    if i eq 0 then
		subfield_sequence := PrimeFreeSequence(m_0 cat [mt], field_exponent); /* subfield = Inv(beta) */
	    else
		subfield_sequence := PrimeFreeSequence(m_0 cat [ms^(field_exponent-i)*mt], field_exponent);
	    end if;
	    ti := Cputime();
	    /* check if norm is already computed */
	    norm_index := Index(Norms_List[1], subfield_sequence); 
	    t_norm +:= Cputime(ti);
	    if ((norm_index ne 0) and (norms_bool)) eq true then
		norm_I := Norms_List[2, norm_index];
	    else
		print "computing norm";
		norm_I := KF_ideal_relative_norm(I, field_sequence, subfield_sequence, beta, field_exponent:determinant:=Determinant(Matrix(I)));
		Append(~Norms_List[1], subfield_sequence);
		Append(~Norms_List[2], norm_I);
	    end if;	
	    subfield_basis_free := KF_primefree_basis(subfield_sequence, field_exponent);
	    /* recursive call to the function */
            G := $$(norm_I, subfield_sequence, field_exponent, subfield_basis_free, precision_log, []: Units_List := Units_List1, Norms_List := Norms_List, norms_bool := true);
	    delete norm_I;
	    /* extend result to field */
	    G := Complete_extension([G], subfield_sequence, subfield_basis_free, field_sequence, field_basis_free, field_exponent)[1];
	    delete subfield_basis_free;
	    K := KF_creation(field_sequence, field_exponent);
	    /* update g with found G */
	    g[1] := NFelement_to_vector1(Vector_to_NFelement1(g[1], field_sequence, field_exponent:KF:=K)*Vector_to_NFelement1(G[1], field_sequence, field_exponent:KF:=K), field_sequence, field_exponent);
	    g[2] := ElementToSequence(Vector(g[2])+Vector(G[2]));
	    delete K, G;
	    print "PIP on", i+1, "th norm calculated";
	end for;
	
	print "last norm to do";
	beta[n-1] := 0;
	beta[n] := 1; /* beta is sigma_(n) */
	subfield_sequence := m_0 cat [ms];
	norm_index := Index(Norms_List[1], subfield_sequence);
	if ((norm_index ne 0) and (norms_bool)) eq true then
	    norm_I := Norms_List[2, norm_index];
	else
	    ti := Cputime();
	    norm_I := KF_ideal_relative_norm(I, field_sequence, subfield_sequence, beta, field_exponent:determinant:=Determinant(Matrix(I)));
	    t_norm +:= Cputime(ti);
	    Append(~Norms_List[1], subfield_sequence);
	    Append(~Norms_List[2], norm_I);
	end if;
	subfield_basis_free := KF_primefree_basis(subfield_sequence, field_exponent);
	G := $$(norm_I, subfield_sequence, field_exponent, subfield_basis_free, precision_log, []: Units_List := Units_List1, Norms_List := Norms_List, norms_bool := true);
	delete norm_I;
	/* extend to field */
	G := Complete_extension([G], subfield_sequence, subfield_basis_free, field_sequence, field_basis_free, field_exponent)[1];
	delete subfield_basis_free;
	K := KF_creation(field_sequence, field_exponent);
	h1 := ZeroSequence(Rationals(), field_dim)  cat ZeroSequence(Rationals(), (field_exponent-2)*field_dim);
	h1[1] := 1;
	h2 := ZeroSequence(Rationals(), field_dim);
	for i := 1 to (field_exponent-1) do
	    beta[n-1] := i;
	    beta[n] := 0;
	    h1 := Galois_closure_multiplication(h1, Galois_morphism_closure(G[1], beta, field_sequence, field_exponent), field_sequence, field_exponent);
	    h2 := ElementToSequence(Vector(h2) + Vector(Induced_log_permutation(G[2], beta, field_exponent)));
	end for;
	delete G;
	K := KF_creation(field_sequence, field_exponent);
	g[1] := NFelement_to_vector1(Vector_to_NFelement1(g[1], field_sequence, field_exponent:KF:=K)/Vector_to_NFelement1(h1[1..field_dim], field_sequence, field_exponent:KF:=K), field_sequence, field_exponent);
	g[2] := ElementToSequence(Vector(g[2]) - Vector(h2));
	delete K, h1, h2;
	/* will reduce dound gen g with babai  */
	g := KF_RedGen(g, U, field_sequence, field_exponent);
	print "precision before GEN-from_Power is: ", precision;
	g, precision, lattice, uni := KF_Ideal_Gen_From_power(g, field_sequence, field_exponent, precision_log, U, field_basis_free: precision := precision, lattice := lattice, uni := uni, bool := bool);
	g, t_decod, t_recons := KF_RedGen(g, U, field_sequence, field_exponent: red_method:=red_method);
	return g, [t_norm, t_decod, t_recons], precision, lattice, uni;
    end if;
end function;


Simple_relative_PIP_integralbasis := function(I, ground_field, extension, precision_log, U: depth := 1, Units_list := [* [* *], [* *] *], Norms_list := [* [* *],  [* *] *], precision := 1, lattice:=Relative_real_basis_lattice_init(ground_field, extension), uni:=IdentityMatrix(Rationals(), Relative_extension_dimension(ground_field, extension)[1]), norms_bool := false)
    a := KF_is_simple(ground_field);
    b := KF_is_simple(extension);
    t_norm := 0;
    if (a and b) then
	/* creation of field and order */
	K := Relative_extension_creation(ground_field, extension);
	O := (MaximalOrder(K));
	/* creation of ideal in order */
	J := [Relative_vector_to_NFelement1(I[i], ground_field, extension:KE:=K) : i in [1..#I]];
	J := ideal<O|J>;
	/* solve PIP with black box */
	t, g := IsPrincipal(J);
	/* "*************** minimal subfield ****************"; */
	/* Come back to sequence representation */
	h1 := Relative_NFelement_to_vector1((K ! g), ground_field, extension);
	h2 := Relative_Log_embedding(h1, ground_field, extension, precision_log);
	return [h1, h2];
    elif (a and (not b)) then
	if U eq [] then
	    index := Index(Units_list[1], [ground_field, extension]);
	    print "index for", [ground_field, extension], ":", index;
	    if index ne 0 then
		U := Units_list[2, index];
	    else
		U := Relative_units_real(ground_field, extension, precision_log:depth:=depth);
		Append(~Units_list[1], [ground_field, extension]);
		Append(~Units_list[2], U);
	    end if;
	end if;
	field_dim := Relative_extension_dimension(ground_field, extension)[1];
	/* define needed objects */
	ms := extension[1][#extension[1]-1];
	mt := extension[1][#extension[1]];
	m_0 := Prune(Prune(extension[1]));
	beta_ground := ZeroSequence(Integers(), #ground_field[1]);
	beta_ext := ZeroSequence(Integers(), #extension[1]);
	g := [ZeroSequence(Rationals(), field_dim), ZeroSequence(Rationals(), field_dim)];
	g[1,1] := 1;
	for i := 0 to (extension[2]-1) do
	    /* define morphism beta which is sigma_(n-1)sigma_n^i */
	    beta_ext[#extension[1]-1] := 1;			
	    beta_ext[#extension[1]] := i;
	    beta := [beta_ground, beta_ext];
	    /* define subextension = Inv(beta) */
	    subextension := <m_0 cat [ms^(-i mod extension[2])*mt], extension[2]>;
	    /* look if norm has already been calculated */
	    /* then calculate the norm (if desired?) */
	    norm_index := Index(Norms_list[1], [ground_field, subextension]);
	    t := Cputime();
	    if ((norm_index ne 0) and (norms_bool)) eq true then
		norm_I := Norms_list[2, norm_index];
	    else
		norm_I := Relative_ideal_relative_norm(I, beta, ground_field, subextension, extension: determinant:=Determinant(Matrix(I)));
		Append(~Norms_list[1], [ground_field, subextension]);
		Append(~Norms_list[2], norm_I);
	    end if;
	    t_norm +:= Cputime(t);
	    /* "**********************************"; */
	    /* recursively solve PIP on norm_I */
	    G := $$(norm_I, ground_field, subextension, precision_log, []: Units_list := Units_list, Norms_list := Norms_list, precision:= 1, norms_bool := norms_bool);
	    delete norm_I;
	    /* put retrieved element in the big field */
	    G := Relative_complete_extension([G], ground_field, subextension, extension)[1];
	    /* multiply the product of elements by the latest retrieved */
	    K := Relative_extension_creation(ground_field, extension);
	    g[1] := Relative_NFelement_to_vector1(Relative_vector_to_NFelement1(g[1], ground_field, extension:KE:=K)*Relative_vector_to_NFelement1(G[1], ground_field, extension:KE:=K), ground_field, extension);
	    g[2] := ElementToSequence(Vector(g[2])+Vector(G[2]));
	    delete K, G;
	end for;
	/* will do computations for last norm */
	/* define morphism beta which is sigma_(n) */
	beta_ext[#extension[1]-1] := 0;			
	beta_ext[#extension[1]] := 1;
	beta := [beta_ground, beta_ext];
	/* define subextension = Inv(beta) */
	subextension := <m_0 cat [ms], extension[2]>;
	/* look if norm has already been calculated */
	/* then calculate the norm (if desired?) */
	norm_index := Index(Norms_list[1], [ground_field, subextension]);
	t := Cputime();
	if ((norm_index ne 0) and (norms_bool)) eq true then
	    norm_I := Norms_list[2, norm_index];
	else
	    norm_I := Relative_ideal_relative_norm(I, beta, ground_field, subextension, extension /*: determinant:=Determinant(Matrix(I)) */);
	    Append(~Norms_list[1], [ground_field, subextension]);
	    Append(~Norms_list[2], norm_I);
	end if;
	t_norm +:= Cputime(t);
	/* print "starting to solve PIP of given norm"; */
	G := $$(norm_I, ground_field, subextension, precision_log, []: Units_list := Units_list, Norms_list := Norms_list, precision:= 1, norms_bool := norms_bool);
	delete norm_I;
	/* put retrieved element in the big field */
	G := Relative_complete_extension([G], ground_field, subextension, extension)[1];
	/* will calculate the element in denominator of formulae */
	h1 := ZeroSequence(Rationals(), field_dim)  cat ZeroSequence(Rationals(), ((ground_field[2]-1)*(extension[2]-1)-1)*field_dim);
	h1[1] := 1;
	h2 := ZeroSequence(Rationals(), field_dim);
	for i := 1 to (extension[2]-1) do
	    beta_ext[#extension[1]-1] := i;
	    beta_ext[#extension[1]] := 0;
	    beta := [beta_ground, beta_ext];
	    h1 := Relative_galois_closure_multiplication(h1, Relative_galois_morphism_closure(G[1], beta, ground_field, extension), ground_field, extension);
	    //print h1, "after mult in denominator";
	    h2 := ElementToSequence(Vector(h2) + Vector(Relative_log_permutation(G[2], beta, ground_field, extension)));
	end for;
	delete G;
	K := Relative_extension_creation(ground_field, extension);
	g[1] := Relative_NFelement_to_vector1(Relative_vector_to_NFelement1(g[1], ground_field, extension:KE:=K)/Relative_vector_to_NFelement1(h1[1..field_dim], ground_field, extension:KE:=K), ground_field, extension);

	g[2] := ElementToSequence(Vector(g[2]) - Vector(h2));
	delete K, h1, h2;

	g, V, precision, lattice, uni := Relative_Ideal_Gen_From_power(g, ground_field, extension, precision_log, U: Units_list := Units_list, depth:=depth, precision:=precision, basis_lattice:=lattice, unitary:=uni);
	g, t_decod, t_recons := Relative_reduction_generator(g, V, ground_field, extension) ;
	return g, [t_norm, t_decod, t_recons], precision, lattice, uni;
    elif (not a) and b then
	ground1 := extension;
	ext1 := ground_field;
	if U eq [] then
    	    index := Index(Units_list[1], [ground1, ext1]);
	    /* print "index", index; */
    	    if index ne 0 then
    		U := Units_list[2, index];
    	    else
    		U := Relative_units_real(ground1, ext1, precision_log:depth:=depth);
    		Append(~Units_list[1], [ground1, ext1]);
    		Append(~Units_list[2], U);
    	    end if;
	    U1 := [U[i,1] : i in [1..#U]];
	    U2 := [U[i,2] : i in [1..#U]];
	else
	    U1 := [U[i,1] : i in [1..#U]];
	    U2 := [U[i,2] : i in [1..#U]];
	    U1 := Relative_swap_field_rep_family(U1, ground_field, extension);
	    U2 := Relative_swap_field_rep_family(U2, ground_field, extension);
	end if;
	I1 := Relative_swap_field_rep_family(I, ground_field, extension);
	V := [[U1[i], U2[i]] : i in [1..#U]];
	g, T, precision, lattice, uni := $$(I1, ground1, ext1, precision_log, V: Units_list := Units_list, Norms_list := Norms_list, precision:= 1, norms_bool := norms_bool);
	return [Relative_swap_field_rep(g[1], ground1, ext1), Relative_swap_field_rep(g[2], ground1, ext1)], T, precision, lattice, uni;
    end if;
end function;


Relative_PIP_integralbasis := function(I, ground_field, extension, precision_log, U: depth := 1, Units_list := [* [* *], [* *] *], Norms_list := [* [* *],  [* *] *], precision := 1, lattice:=Relative_real_basis_lattice_init(ground_field, extension), uni:=IdentityMatrix(Rationals(), Relative_extension_dimension(ground_field, extension)[1]), norms_bool := false)
    a := KF_is_simple(ground_field);
    b := KF_is_simple(extension);
    time_norm := 0;
    if a or b then
	return Simple_relative_PIP_integralbasis(I, ground_field, extension, precision_log, U: depth := depth, Units_list:=Units_list, Norms_list := Norms_list, precision := precision, lattice:=lattice, uni:=uni, norms_bool := norms_bool);
    else
	if U eq [] then
	    index := Index(Units_list[1], [ground_field, extension]);
	    if index ne 0 then
		U := Units_list[2, index];
	    else
		U := Relative_units_real(ground_field, extension, precision_log:depth:=depth);
		Append(~Units_list[1], [ground_field, extension]);
		Append(~Units_list[2], U);
	    end if;
	end if;
	field_dim := Relative_extension_dimension(ground_field, extension)[1];
	/* define needed objects */
	ms := extension[1][#extension[1]-1];
	mt := extension[1][#extension[1]];
	m_0 := Prune(Prune(extension[1]));
	beta_ground := ZeroSequence(Integers(), #ground_field[1]);
	beta_ext := ZeroSequence(Integers(), #extension[1]);
	g := [ZeroSequence(Rationals(), field_dim), ZeroSequence(Rationals(), field_dim)];
	g[1,1] := 1;
	for i := 0 to (extension[2]-1) do
	    /* define morphism beta which is sigma_(n-1)sigma_n^i */
	    beta_ext[#extension[1]-1] := 1;			
	    beta_ext[#extension[1]] := i;
	    beta := [beta_ground, beta_ext];
	    /* define subextension = Inv(beta) */
	    subextension := <m_0 cat [ms^(-i mod extension[2])*mt], extension[2]>;
	    /* look if norm has already been calculated */
	    /* then calculate the norm (if desired?) */
	    norm_index := Index(Norms_list[1], [ground_field, subextension]);
	    if ((norm_index ne 0) and (norms_bool eq true)) then
		norm_I := Norms_list[2, norm_index];
	    else
		t_norm := Cputime();
		norm_I := Relative_ideal_relative_norm(I, beta, ground_field, subextension, extension/* : determinant:=Determinant(Matrix(I)) */);
		time_norm +:= Cputime(t_norm);
		/* print "ideal norm computed in:", ground_field, extension, Cputime(t_norm); */
		Append(~Norms_list[1], [ground_field, subextension]);
		Append(~Norms_list[2], norm_I);
	    end if;
	    
	    /* "**********************************"; */
	    /* recursively solve PIP on norm_I */
	    G := $$(norm_I, ground_field, subextension, precision_log, []: Units_list := Units_list, Norms_list := Norms_list, precision:= 1, norms_bool := norms_bool);
	    delete norm_I;
	    /* put retrieved element in the big field */
	    G := Relative_complete_extension([G], ground_field, subextension, extension)[1];
	    /* multiply the product of elements by the latest retrieved */
	    K := Relative_extension_creation(ground_field, extension);
	    g[1] := Relative_NFelement_to_vector1(Relative_vector_to_NFelement1(g[1], ground_field, extension:KE:=K)*Relative_vector_to_NFelement1(G[1], ground_field, extension:KE:=K), ground_field, extension);
	    g[2] := ElementToSequence(Vector(g[2])+Vector(G[2]));
	    delete K, G;
	end for;
	/* will do computations for last norm */
	/* define morphism beta which is sigma_(n) */
	beta_ext[#extension[1]-1] := 0;			
	beta_ext[#extension[1]] := 1;
	beta := [beta_ground, beta_ext];
	/* define subextension = Inv(beta) */
	subextension := <m_0 cat [ms], extension[2]>;
	/* look if norm has already been calculated */
	/* then calculate the norm (if desired?) */
	norm_index := Index(Norms_list[1], [ground_field, subextension]);
	if ((norm_index ne 0) and (norms_bool)) eq true then
	    norm_I := Norms_list[2, norm_index];
	else
	    t_norm := Cputime();
	    norm_I := Relative_ideal_relative_norm(I, beta, ground_field, subextension, extension: determinant:=Determinant(Matrix(I)));
	    time_norm +:= Cputime(t_norm);
	    /* print "ideal norm computed in:", Cputime(t_norm); */
	    Append(~Norms_list[1], [ground_field, subextension]);
	    Append(~Norms_list[2], norm_I);
	end if;
	/* print "starting to solve PIP of given norm"; */
	G := $$(norm_I, ground_field, subextension, precision_log, []: Units_list := Units_list, Norms_list := Norms_list, precision:= 1,  norms_bool := norms_bool);
	delete norm_I;
	/* put retrieved element in the big field */
	G := Relative_complete_extension([G], ground_field, subextension, extension)[1];

	/* will calculate the element in denominator of formulae */
	h1 := ZeroSequence(Rationals(), field_dim)  cat ZeroSequence(Rationals(), ((ground_field[2]-1)*(extension[2]-1)-1)*field_dim);
	h1[1] := 1;
	h2 := ZeroSequence(Rationals(), field_dim);
	for i := 1 to (extension[2]-1) do
	    beta_ext[#extension[1]-1] := i;
	    beta_ext[#extension[1]] := 0;
	    beta := [beta_ground, beta_ext];
	    h1 := Relative_galois_closure_multiplication(h1, Relative_galois_morphism_closure(G[1], beta, ground_field, extension), ground_field, extension);
	
	    h2 := ElementToSequence(Vector(h2) + Vector(Relative_log_permutation(G[2], beta, ground_field, extension)));
	end for;
	delete G;

	K := Relative_extension_creation(ground_field, extension);
	g[1] := Relative_NFelement_to_vector1(Relative_vector_to_NFelement1(g[1], ground_field, extension:KE:=K)/Relative_vector_to_NFelement1(h1[1..field_dim], ground_field, extension:KE:=K), ground_field, extension);
	
	g[2] := ElementToSequence(Vector(g[2]) - Vector(h2));
	delete K, h1, h2;
	g := Relative_reduction_generator(g, U, ground_field, extension);
	g, V, precision, lattice, uni := Relative_Ideal_Gen_From_power(g, ground_field, extension, precision_log, U: Units_list := Units_list, depth:=depth, precision:=precision, basis_lattice:=lattice, unitary:=uni);
	g, t_decod, t_recons := Relative_reduction_generator(g, V, ground_field, extension);
	T := [time_norm, t_decod, t_recons];
	return g, T, precision, lattice, uni;
    end if;
end function;
