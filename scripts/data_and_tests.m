KF_stat_log_norm_key := function(kummer_field, size_key, precision: size_set:=200, U:=[], pruning:=false, p:=1/2, n:=10, shape:="uni", supp:=1, file:="")
    dim := KF_dimension(kummer_field);
    rank := (dim-1) div 2;
    stats := [];
    mi := 0;
    ma := 0;
    q1 := 0;
    q3 := 0;
    me := 0;
    norms := [];
    ec := [];
    rq := size_set div 4;
    rm := size_set div 2;
    prune:= [];
    if pruning then
	prune := [RealField()!(rank-i+1)/rank : i in [1..rank]];
    end if;
    i := 0;
    while #norms lt size_set do
	i := #norms;
	if i mod 10 eq 0 then 
	    print i;
	end if;
	/* if i mod 50 eq 0 then print i; end if; */
	g := Keygen(size_key, dim: shape:=shape, p:=p, n:=n, length_supp:=supp, kum_field:=kummer_field);
	Lg := KF_Log_embedding(g, kummer_field[1], kummer_field[2], precision);
	n_g := RealField(10)!Norm(Vector(Orthogonal_projection(Lg, [Rationals()!1 : j in [1..#g]])));
	/* print RealField(5)!Norm(Vector(Lg)), RealField(5)!n_g; */
	if n_g ne 0 then
	    Append(~norms, n_g);
	    if (U ne []) and (#file ne 0) then
		e := Log_enumeration_cost_kummer(U, size_key, kummer_field: B:=RealField()!n_g, prune:=prune);
		FILE := Open(file, "a");
		fprintf FILE, "%o\n", e;
		delete FILE;
	    end if;
	end if;
    end while;
    Sort(~norms);
    if U ne [] then
	mi +:= Log_enumeration_cost_kummer(U, size_key, kummer_field: B:=RealField()!norms[1]);
	ma +:= Log_enumeration_cost_kummer(U, size_key, kummer_field: B:=RealField()!norms[#norms]);
	q1 := Log_enumeration_cost_kummer(U, size_key, kummer_field: B:=RealField()!norms[rq]);
	me := Log_enumeration_cost_kummer(U, size_key, kummer_field: B:=RealField()!norms[rm]);
	q3 := Log_enumeration_cost_kummer(U, size_key, kummer_field: B:=RealField()!norms[rq+rm]);
	stats := [mi, q1, me, q3, ma];
    end if;
    /* print [norms[1], norms[rq], norms[rm], norms[rm+rq], norms[#norms]]; */
    return [norms[1], norms[rq], norms[rm], norms[rm+rq], norms[#norms]], stats;
end function;


Relative_stat_log_norm_key := function(ground_field, extension, size_key, precision: size_set:=200, U:=[])
    dim := Relative_extension_dimension(ground_field, extension)[1];
    stats := [];
    mi := 0;
    ma := 0;
    q1 := 0;
    q3 := 0;
    me := 0;
    norms := [];
    rq := size_set div 4;
    rm := size_set div 2;
    for i in [1..size_set] do
	g := Keygen_uniform(size_key, dim);
	Lg := Relative_Log_embedding(g, ground_field, extension, precision);
	n_g := Norm(Vector(Orthogonal_projection(Lg, [Rationals()!1 : j in [1..#g]])));
	Append(~norms, n_g);
	/* if U ne [] then */
	/* 	enum_cost +:= Log_enumeration_cost_relative(U, size_key, ground_field, extension: B:=RealField()!n_g); */
	/* end if; */
	/* mean +:= n_g; */
    end for;
    Sort(~norms);
    if U ne [] then
	mi +:= Log_enumeration_cost_relative(U, size_key, ground_field, extension: B:=RealField()!norms[1]);
	ma +:= Log_enumeration_cost_relative(U, size_key, ground_field, extension: B:=RealField()!norms[#norms]);
	q1 := Log_enumeration_cost_relative(U, size_key, ground_field, extension: B:=RealField()!norms[rq]);
	me := Log_enumeration_cost_relative(U, size_key, ground_field, extension: B:=RealField()!norms[rm]);
	q3 := Log_enumeration_cost_relative(U, size_key, ground_field, extension: B:=RealField()!norms[rq+rm]);
    end if;
    stats := [mi, q1, me, q3, ma];    
    /* mean := &+norms/size_set; */
    /* sd := Sqrt(&+[(norms[i]-mean)^2 : i in [1..size_set]]/(size_set-1)); */
    return [norms[1], norms[rq], norms[rm], norms[rm+rq], norms[#norms]], stats;
end function;


KF_attack := function(K, number_keys, size_key, U, precision_log, norms_bool: p:=1/2, n:=10, shape:="uni", supp:=1, list:=[*[* *], [* *]*], lattice:=1, uni:=1, precision:=1, decoding_method:="lll", enum_cost:=false, red_version:="lll")
    number_success := 0;
    number_shorter := 0;

    time_attack := 0;
    time_norm := 0;
    time_decoding := 0;
    time_alg_recons := 0;

    count := 0;
    dim := KF_dimension(K);
    d := K[1];
    field_exponent:=K[2];
    norms_proj := [];
    ec := [];
    
    approx_factors := [];
    af := [];

    file_herm_fact := "./Data_kummer/hermite_fact" cat "_" cat IntegerToString(field_exponent) cat "_" cat red_version cat "_" cat IntegerToString(precision_log);
    
    /* herm_fact_key := []; */
    /* herm_fact_retrieved := []; */

    RR := RealField(6);
    
    for j:= 1 to number_keys do

	g := Keygen(size_key, dim: length_supp := supp, shape:=shape, p:=p, n:=n, kum_field:=<>);
	B := KF_IntegralBasis_creation(g, d, field_exponent);
	/* print "quotient det by alg. norm is: ", Determinant(Matrix(B))/AbsoluteValue(AbsoluteNorm(Vector_to_NFelement1(g, d, field_exponent))); */
	t := Cputime();
	basis_free := KF_primefree_basis(d, field_exponent);
	norms_list := KF_ideal_norm_list(g, d, field_exponent:Ideal_norms_list := [* [* *], [* *] *]);
	
	if enum_cost then
	    Lg := ChangeUniverse(KF_Log_embedding(g, K[1], K[2], precision), RealField(150));
	    n_g := My_proj_norm(Lg, 1: type:="flat");
	    if n_g ne 0 then
		Append(~norms_proj, n_g);
	    end if;
	end if;
	
	a, time_vec, precision, lattice, uni := KF_PIP_integralbasis(B, d, field_exponent, basis_free, precision_log, U: Units_List:=list, Norms_List:=norms_list, norms_bool:= norms_bool, precision:=precision, lattice:=lattice, uni:=uni, red_method:=decoding_method, bool:=true);
	
	time_attack +:= Cputime(t);
	time_norm +:= time_vec[1];
	time_decoding +:= time_vec[2];
	time_alg_recons +:= time_vec[3];
	
	b := CanChangeUniverse(a[1], Integers());
	approx_factor := RealField(6)!Sqrt(Norm(Vector(a[1]))/Norm(Vector(g)));
	if b eq true then
    	    if ((Vector(a[1]) eq Vector(g)) or (Vector(a[1]) eq -Vector(g))) then
    		number_success +:= 1;
		/* Append(~approx_factors, approx_factor); */
            elif approx_factor lt 1 then
    		number_shorter +:=1;
		Append(~approx_factors, approx_factor);
	    else
		Append(~approx_factors, approx_factor);
	    end if;
	else
	    Append(~approx_factors, approx_factor);
	end if;
	
	print "Number of keys retrieved: ", number_success, " over ", j, "\n";
	print "Number of shorter keys retrieved: ", number_shorter, " over ", j, "\n";
	print "Average time for attack is: ", RealField(5)!(time_attack/j), "\n";
	print "Average time for decoding is: ", RealField(5)!(time_decoding/j), "\n";
	print "Average time for reconstruction is: ", RealField(5)!(time_alg_recons/j), "\n";
	if (not norms_bool) then
    	    print "Average time for norm computation is: ", RealField(5)!(time_norm/j), "\n";
	end if;

	/* sv := Root(AbsoluteValue(AbsoluteNorm(Vector_to_NFelement1(g, d, field_exponent))), dim); */
	/* print Sqrt(Norm(Vector(g)))/sv; */

	/* Append(~herm_fact_key, Root(Sqrt(Norm(Vector(g)))/sv, dim)); */
	/* Append(~herm_fact_retrieved, Root(Sqrt(Norm(Vector(a[1])))/sv, dim)); */
	
	/* print herm_fact_key[j]; */
	/* print herm_fact_retrieved[j]; */

	/* FILE := Open(file_herm_fact, "a"); */
	/* fprintf FILE, "%o \t %o \n", RR!Root(Sqrt(Norm(Vector(g)))/sv, dim), RR!Root(Sqrt(Norm(Vector(a[1])))/sv, dim); */
	/* delete FILE; */
	
        Sort(~norms_proj);
        Sort(~approx_factors);

        if #approx_factors gt 10 then
            af := [approx_factors[1], approx_factors[#approx_factors div 4], approx_factors[#approx_factors div 2], approx_factors[3*(#approx_factors div 4)], approx_factors[#approx_factors]];
	    print af;
	end if;
    end for;
    
    Sort(~norms_proj);
    Sort(~approx_factors);

    if #approx_factors gt 10 then
	af := [approx_factors[1], approx_factors[#approx_factors div 4], approx_factors[#approx_factors div 2], approx_factors[3*(#approx_factors div 4)], approx_factors[#approx_factors]];
    end if;
    
    if enum_cost then
	ec := [norms_proj[1], norms_proj[number_keys div 2], norms_proj[#norms_proj]];
	ec := [Log(2, EnumerationCost(LogLattice_creation(U), ec[i]^2)) : i in [1..#ec]];
    end if;

    return [number_success, number_shorter], ec, af, precision, lattice, uni;
end function;



Relative_attack := function(Kg, Ke, number_keys, size_key, U, precision_log, norms_bool: p:=1/2, n:=10, shape:="uni", supp:=1, list:=[*[* *], [* *]*], lattice:=1, uni:=1, precision:=1, decoding_method:="lll", depth := 1, enum_cost := false)
    number_success := 0;
    number_shorter := 0;
    
    time_attack := 0;
    time_norm := 0;
    time_decoding := 0;
    time_alg_recons := 0;
    
    count := 0;
    dim := Relative_extension_dimension(Kg, Ke)[1];
    norms_proj := [];
    ec := [];

    af := [];
    approx_factors := [];

    RR := RealField(6);

    
    for j in [1..number_keys] do
	g := Keygen(size_key, dim: length_supp := supp, shape:=shape, p:=p, n:=n, kum_field:=<>);
	norm_list:= Relative_ideal_norm_list(g, Kg, Ke);
	I := Relative_IntegralBasis_creation(g, Kg, Ke);

	if enum_cost then
	    Lg := ChangeUniverse(Relative_Log_embedding(g, Kg, Ke, precision), RealField(precision div 3));
	    n_g := My_proj_norm(Lg, 1: type:="flat");
	    if n_g ne 0 then
		Append(~norms_proj, n_g);
	    end if;
	end if;
	
	t := Cputime();
	a, time_vec, precision, lattice, uni := Relative_PIP_integralbasis(I, Kg, Ke, precision_log, U: Units_list := list, norms_bool:=norms_bool, Norms_list:=norm_list, depth:=depth, precision:=precision, lattice:=lattice, uni:=uni);

	time_attack +:= Cputime(t);
	time_norm +:= time_vec[1];
	time_decoding +:= time_vec[2];
	time_alg_recons +:= time_vec[3];

	b := CanChangeUniverse(a[1], Integers());
	approx_factor := RealField(6)!Sqrt(Norm(Vector(a[1]))/Norm(Vector(g)));
	/* b:=true; */
	if b eq true then
    	    if ((Vector(a[1]) eq Vector(g)) or (Vector(a[1]) eq -Vector(g))) then
    		number_success +:= 1;
            elif approx_factor lt 1 then
    		number_shorter +:=1;
		Append(~approx_factors, approx_factor);
	    else
		Append(~approx_factors, approx_factor);
	    end if;
	else
	    Append(~approx_factors, approx_factor);
	end if;
	
	print "Number of keys retrieved: ", number_success, " over ", j, "\n";
	print "Number of shorter keys retrieved: ", number_shorter, " over ", j, "\n";
	print "Average time for attack is: ", RealField(5)!(time_attack/j), "\n";
	print "Average time for decoding is: ", RealField(5)!(time_decoding/j), "\n";
	print "Average time for reconstruction is: ", RealField(5)!(time_alg_recons/j), "\n";

	if (not norms_bool) then
    	    print "Average time for norm computation is: ", RealField(5)!(time_norm/j), "\n";
	end if;
    end for;
    Sort(~norms_proj);
    if enum_cost then
	ec := [norms_proj[1], norms_proj[#norms_proj div 4], norms_proj[#norms_proj div 2], norms_proj[(3*#norms_proj) div 4], norms_proj[#norms_proj]];
	ec := [Log(2, EnumerationCost(LogLattice_creation(U), ec[i]^2)) : i in [1..#ec]];
    end if;
    
    if #approx_factors gt 10 then
        af := [approx_factors[1], approx_factors[#approx_factors div 4], approx_factors[#approx_factors div 2], approx_factors[3*(#approx_factors div 4)], approx_factors[#approx_factors]];
	    print af;
    end if;

    return [number_success, number_shorter], ec, af;
end function;


KF_attack_naive := function(K, number_keys, size_key: red_method:="lll")
    number_success := 0;
    number_generators := 0;
    number_shorter := 0;

    time_attack := 0;

    count := 0;
    dim := KF_dimension(K);
    d := K[1];
    field_exponent := K[2];
    norms_proj := [];
    ec := [];
    
    file_herm_fact := "./Data_kummer/hermite_fact_naive" cat "_" cat IntegerToString(field_exponent) cat "_" cat red_method;
    
    /* herm_fact_key := []; */
    /* herm_fact_retrieved := []; */

    RR := RealField(6);

    L := KF_creation(K[1], K[2]);
    
    for j:= 1 to number_keys do

	g := Keygen(size_key, dim);
	B := KF_IntegralBasis_creation(g, d, field_exponent);
	B := Matrix(B);

	sv := Root(AbsoluteValue(AbsoluteNorm(Vector_to_NFelement1(g, d, field_exponent))), dim);
		
	print "before reduction";

	t := Cputime();

	B := LLL(B);
	print "after lll";
	if red_method eq "bkz" then
	    B := Fplll(B);
	end if;
	print "after bkz";
	N := Norms(B);

	/* n_min, ind := Min(N); */
	
	n_min := Max(Norms(B))+1;
	b_min := ZeroSequence(Rationals(), dim);
	
	for ind in [1..Nrows(B)] do
	    a := Eltseq(B[ind]);
	    if Abs(AbsoluteNorm(Vector_to_NFelement1(g, K[1], K[2]: KF:=L)/Vector_to_NFelement1(a, K[1], K[2]: KF:=L))) eq 1 then
		print "generator detected";
		
		if Norm(Vector(a)) lt n_min then
		    n_min := Norm(Vector(a));
		    b_min := a;
		end if;

	    end if;
	end for;

	
	
	time_attack +:= Cputime(t);

	
	if b_min ne ZeroSequence(Rationals(), dim) then
	    number_generators +:= 1;
	    hermite_factor := RR!Root(Sqrt(Norm(Vector(b_min)))/sv, dim);
	    if ((Vector(b_min) eq Vector(g)) or (Vector(b_min) eq -Vector(g))) then
		number_success +:= 1;
	    elif n_min lt Norm(Vector(g)) then
		number_shorter +:= 1;
	    end if;
	    
	    print "hermite factor is: ", hermite_factor;

	    FILE := Open(file_herm_fact, "a");
	    fprintf FILE, "%o \t %o \n", RR!Root(Sqrt(Norm(Vector(g)))/sv, dim), RR!Root(Sqrt(Norm(Vector(b_min)))/sv, dim);
	    delete FILE;
	    
	end if;


	print "hermite factor of shortest vector is: ", RR!Root(Sqrt(Min(Norms(B)))/sv, dim);
    

	print "Number of generators retrieved: ", number_generators, " over ", j, "\n";
	print "Number of shorter retrieved: ", number_shorter, " over ", j, "\n";
	print "Number of keys retrieved: ", number_success, " over ", j, "\n";
	print "Average time for attack is: ", RealField(5)!(time_attack/j), "\n";
	
    end for;
    
    return number_success, number_generators;
end function;




/* ############################################################################################ */
/* ############################################################################################ */
/* ############################################################################################ */
/* ############################################################################################ */


Ideal_norm_data_principal := function(dim_1, dim_2, size_coeff, number_ideals)
    TIME_TWO_EL := [];
    TIME_MAGMA_NET := [];
    TIME_MAGMA := [];
    p<x> := PolynomialRing(Integers());
    pol_1 := p!Pol_field_creation(dim_1, size_coeff);
    print "ground field created";
    K := NumberField(pol_1: Check:=false);
    time OK := MaximalOrder(K);
    basis_sub := AbsoluteBasis(K);
    /* local q, y; */
    q<y> := PolynomialRing(OK);
    time pol := q!Pol_creation_field(K, dim_2, size_coeff);
    pol +:= y^dim_2;
    while (not IsIrreducible(q!pol)) do
	pol := q!Pol_creation_field(K, dim_2, size_coeff);
	pol +:= y^dim_2;
	/* pol := Pol_field_creation(extensions_dim[i], size_coeff); */
    end while;
    print "extension created";
    L := ext<K|pol>;
    OL := EquationOrder(pol);
    /* OL := MaximalOrder(L); */
    IsIsomorphic(FieldOfFractions(OL), L);
    time basis := AbsoluteBasis(OL);
    /* readi hbjhbh; */
    /* time OLabs := AbsoluteOrder(OL); */
    /* time Kabs:= AbsoluteField(K); */
    /* time OKabs := MaximalOrder(Kabs); */
    print "all orders created";

    dim := dim_1*dim_2;
    count := 0;
    for i in [1..number_ideals] do
	i;
	g_abs := ChangeUniverse(Keygen_uniform(1, dim), Integers());
	B := Integral_basis_principal(g_abs, basis, OL);
	print "HNF created";
	/* Determinant(Matrix(I)), Determinant(H); */
	s := Cputime();
	Habs := Relative_norm_prob(B, OK, OL, OK, basis_sub);
	Append(~TIME_TWO_EL, Cputime(s));

	s := Cputime();
	B1 := Ideal_two_elements(B, basis, OL);
	I := ideal<OL|[Vec_to_order(B1[i], OL) : i in [1..#B1]]>;
	t := Cputime();
	print "ideal generated";
	/* t := Cputime(s); */
	J := Norm(I);
	Append(~TIME_MAGMA_NET, Cputime(t));
	
	B1 := AbsoluteBasis(J);
	Append(~TIME_MAGMA, Cputime(s));
	
	C := [OK!B1[i] : i in [1..#B1]];
	C := [ChangeUniverse(Eltseq(C[i]), Integers()) : i in [1..#C]];
	if Habs eq HermiteForm(Matrix(C)) then count +:= 1; end if;
	print Determinant(Habs), Determinant(Matrix(B)), Determinant(Matrix(C));
	/* print TIME_MAGMA_NET, TIME_TWO_EL; */
    end for;
    /* return TIME_TWO_EL; */
    return TIME_MAGMA, TIME_MAGMA_NET, TIME_TWO_EL, count;
end function;



Ideal_norm_data := function(dim_1, dim_2, size_coeff, number_ideals)
    TIME_PROBA := [];
    TIME_MAGMA_NET := [];
    TIME_MAGMA := [];
    p<x> := PolynomialRing(Integers());
    pol_1 :=p!Pol_field_creation(dim_1, size_coeff);
    print "ground field created";
    K := NumberField(pol_1: Check:=false);
    time OK := MaximalOrder(K);
    /* local q, y; */
    q<y> := PolynomialRing(OK);
    time pol := q!Pol_creation_field(K, dim_2, size_coeff);
    pol +:= y^dim_2;
    while (not IsIrreducible(q!pol)) do
	pol := q!Pol_creation_field(K, dim_2, size_coeff);
	pol +:= y^dim_2;
	/* pol := Pol_field_creation(extensions_dim[i], size_coeff); */
    end while;
    print "extension created";
    L := ext<K|pol>;
    /* OL := EquationOrder(pol); */
    OL := MaximalOrder(L);
    IsIsomorphic(FieldOfFractions(OL), L);
    time basis := AbsoluteBasis(OL);
    /* readi hbjhbh; */
    /* time OLabs := AbsoluteOrder(OL); */
    /* time Kabs:= AbsoluteField(K); */
    /* time OKabs := MaximalOrder(Kabs); */
    print "all orders created";
    dim := dim_1*dim_2;
    count := 0;
    for i in [1..number_ideals] do
	i;
	g_abs := ChangeUniverse(Keygen_uniform(1, dim), Integers());
	B := Integral_basis_principal(g_abs, basis, OL);
	/* Determinant(Matrix(I)), Determinant(H); */
	s := Cputime();
	Habs := Relative_norm_prob(B, OK, OL, OK, basis);
	Append(~TIME_PROBA, Cputime(s));

	s := Cputime();
	B := Ideal_two_elements(B, basis, OL);
	I := ideal<OL|[Vec_to_order(B[i], OL) : i in [1..#B]]>;
	t := Cputime();
	print "ideal generated";
	/* t := Cputime(s); */
	J := Norm(I);
	Append(~TIME_MAGMA_NET, Cputime(t));
	
	B := AbsoluteBasis(J);
	Append(~TIME_MAGMA, Cputime(s));
	
	C := [OK!B[i] : i in [1..#B]];
	C := [ChangeUniverse(Eltseq(C[i]), Integers()) : i in [1..#C]];
	if Habs eq HermiteForm(Matrix(C)) then count +:= 1; end if;
	print TIME_MAGMA_NET, TIME_PROBA;
    end for;
    /* return TIME_TWO_EL; */
    return TIME_MAGMA, TIME_MAGMA_NET, TIME_PROBA, count;
end function;




/* ############################################################### */
/* ###################### CYCLOTOMIC FIELDS ####################### */
/* ############################################################### */


Ideal_norm_data_principal_cyclo := function(prime, exp, size_coeff, number_ideals)
    TIME_TWO_EL := [];
    TIME_MAGMA_NET := [];
    TIME_MAGMA := [];
    p<x> := PolynomialRing(Integers());
    K := CyclotomicField(prime^exp);
    time OK := MaximalOrder(K);
    basis_sub := AbsoluteBasis(OK);
    /* local q, y; */
    q<y> := PolynomialRing(OK);
    time pol := q!(y^prime-(OK!K.1));
    /* L := ext<K|pol>; */
    OL := EquationOrder(pol: Check:=false);
    L := CyclotomicField(prime^(exp+1));
    /* IsIsomorphic(FieldOfFractions(OL), L); */
    /* OL1 := MaximalOrder(L); */
    time basis := AbsoluteBasis(OL);
    /* readi hbjhbh; */
    time OLabs := AbsoluteOrder(OL);
    print "all orders created";

    dim := prime^(exp);
    print AbsoluteDegree(L);
    count := 0;
    for i in [1..number_ideals] do
	i;
	/* g_abs := ChangeUniverse(Keygen_uniform(1, dim), Integers()); */
	g_abs := 0;
	while g_abs eq 0 do
	    g_abs := OLabs!Random(OL, 2);
	end while;
	g_abs := Eltseq(g_abs);
	print dim;
	/* readi hjbhbjhb; */
	time B := Integral_basis_principal(g_abs, basis, OL);
	/* Determinant(Matrix(I)), Determinant(H); */
	s := Cputime();
	time Habs := Relative_norm_prob(B, OK, OL, OK, basis_sub);
	Append(~TIME_TWO_EL, Cputime(s));
	print(TIME_TWO_EL);
	print "norm computed";
	/* readi hjbj; */

	s := Cputime();
	B := Ideal_two_elements(B, basis, OL);
	print "two el. rep. computed";
	I := ideal<OL|[Vec_to_order(B[i], OL) : i in [1..#B]]>;
	t := Cputime();
	print "ideal generated";
	/* t := Cputime(s); */
	J := Norm(I);
	Append(~TIME_MAGMA_NET, Cputime(t));
	print "norm computed";
	
	B := AbsoluteBasis(J);
	Append(~TIME_MAGMA, Cputime(s));
	
	C := [OK!B[i] : i in [1..#B]];
	C := [ChangeUniverse(Eltseq(C[i]), Integers()) : i in [1..#C]];
	if Habs eq HermiteForm(Matrix(C)) then count +:= 1; end if;
	print count;
	/* readi jnkn; */
	/* print TIME_MAGMA_NET, TIME_TWO_EL; */
    end for;
    /* return TIME_TWO_EL; */
    return TIME_MAGMA, TIME_MAGMA_NET, TIME_TWO_EL, count;
end function;



Ideal_norm_data_cyclo := function(prime, exp, n_p, s_p, range_exp, number_ideals)
    TIME_TWO_EL := [];
    TIME_MAGMA_NET := [];
    TIME_MAGMA := [];
    p<x> := PolynomialRing(Integers());
    K := CyclotomicField(prime^exp);
    time OK := MaximalOrder(K);
    basis_sub := AbsoluteBasis(OK);
    /* local q, y; */
    q<y> := PolynomialRing(OK);
    pol := q!(y^prime-(OK!K.1));
    /* L := ext<K|pol>; */
    OL := EquationOrder(pol: Check:=false);
    L := AbsoluteField(FieldOfFractions(OL));
    L1 := CyclotomicField(prime^(exp+1));
    /* IsIsomorphic(FieldOfFractions(OL), L); */
    OLabs := AbsoluteOrder(OL);
    basis := AbsoluteBasis(OL);
    print "all orders created";
    dim := prime^(exp);
    count := 0;
    for i in [1..number_ideals] do
	i;
	time B, prime_drawn := IntegralIdeal_creation(OLabs, L1, n_p, s_p, range_exp);
	B := HermiteForm(ChangeRing(Matrix(B), Integers()));
	print prime_drawn, Factorisation(Determinant(B));
	B := [Eltseq(B[i]) : i in [1..Nrows(B)]];
	B := [Order_to_vec(OL!(L!B[i])) : i in [1..#B]];
	B := HermiteForm(ChangeRing(Matrix(B), Integers()));
	print prime_drawn, Factorisation(Determinant(B));
	/* readi jhencfjh; */
	B := [Eltseq(B[i]) : i in [1..Nrows(B)]];
	/* print B; */
	s := Cputime();
	time Habs := Relative_norm_prob(B, OK, OL, OK, basis_sub);
	Append(~TIME_TWO_EL, Cputime(s));
	print(TIME_TWO_EL);
	/* readi hjbj; */

	
	s := Cputime();
	B := Ideal_two_elements(B, basis, OL);
	I := ideal<OL|[Vec_to_order(B[i], OL) : i in [1..#B]]>;
	t := Cputime();
	print "ideal generated";
	/* t := Cputime(s); */
	J := Norm(I);
	Append(~TIME_MAGMA_NET, Cputime(t));
	print "norm computed";
	print TIME_MAGMA_NET;
	
	B := AbsoluteBasis(J);
	Append(~TIME_MAGMA, Cputime(s));
	
	C := [OK!B[i] : i in [1..#B]];
	C := [ChangeUniverse(Eltseq(C[i]), Integers()) : i in [1..#C]];
	if Habs eq HermiteForm(Matrix(C)) then count +:= 1; end if;
	/* print TIME_MAGMA_NET, TIME_TWO_EL; */
    end for;
    /* return TIME_TWO_EL; */
    return TIME_MAGMA, TIME_MAGMA_NET, TIME_TWO_EL, count;
end function;
