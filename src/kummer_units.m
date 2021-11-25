/* Compute a generating family of the units defined by e */
/* and controlled by d given the subgroup U such that */
/* OK^p < U < OK ; precision in Log is l */
/* cube roots are computed with real lattice */
Subgroup_from_power_real := function(U, field_sequence, field_exponent, basis_free, precision_log, bool:precision := 1, sublattice := 1, uni := 1, red_version:="lll")
    t := Cputime();
    r := #U;
    W1 := [ U[i, 1] : i in [1..r] ];
    W2 := [ U[i, 2] : i in [1..r] ];
    print "starting computing characters";
    M := EnoughCharacters(W1, field_sequence, field_exponent);
    K := KernelMatrix(Transpose(M));
    K := ChangeRing(K, IntegerRing());
    rank := Rank(K);
    K := HermiteForm(LLL(K));
    K := ChangeRing(K, GF(field_exponent));
    K := ChangeRing(K, IntegerRing());
    print "The kernel matrix has been computed";
    Cputime(t);
    L := KF_creation(field_sequence, field_exponent);
    print rank;
    if rank eq 0 then
	return U, precision, sublattice, uni, 0;
    else
	V1 := []; V2 := []; V3 := [];
	print "starting to compute the roots";
	for i in [1..rank] do
	    Append(~V1, KF_exponentiation(W1, [K[i,j] : j in [1..r]], field_sequence, field_exponent:KF:=L));
	    Append(~V2, ElementToSequence( (&+ [ (K[i, j])* Vector(W2[j]) : j in [1..r] ]) ) );
	end for;

	W := [];
	time_cube_kernel := Cputime(t);
	time_cube_root := 0;
	NORMS1 := [];

	X := [ [V1[i], V2[i] ] : i in [1..rank] ];
	print "starting the reduction in Log";
	if bool eq true then
	    X := Power_Logreduction(X, U, field_sequence, field_exponent/* : red_version := red_version */);
	end if;
	print "reduction in Log finished";
	Sort_Vectornorm(~X);
	V1 := [X[i,1] : i in [1..#X]];
	V3 := [ElementToSequence(Vector(X[i,2])/field_exponent) : i in [1..#X]];    
	s := Cputime();
	depth := KF_depth(<field_sequence, field_exponent>);
	if depth gt 0 then
	    V, precision, lattice, uni := Real_root_family_depth(V1, field_sequence, field_exponent, basis_free: precision:=precision, lattice:=sublattice, unitary := uni, bool := bool, depth:=depth);
	else
	    V, precision, lattice, uni := Real_root_family(V1, field_sequence, field_exponent, basis_free: precision:=precision, lattice:=sublattice, unitary := uni, bool := bool);
	end if;
	W := [ [V[i], V3[i] ] : i in [1..#V1] ];
	time_roots := Cputime(s);
	return U cat W, precision, lattice, uni, rank;
    end if;
end function;


Relative_detect_powers := function(U, ground_field, extension)
    t := Cputime();
    r := #U;
    W1 := [ U[i, 1] : i in [1..r] ];
    W2 := [ U[i, 2] : i in [1..r] ];
    M := Relative_EnoughCharacters(W1, ground_field, extension);
    K := KernelMatrix(Transpose(M));
    K := ChangeRing(K, IntegerRing());
    rank := Rank(K);
    K := LLL(K);
    K := ChangeRing(K, GF(extension[2]));
    K := ChangeRing(K, IntegerRing());
    print "The kernel matrix has been calculated";
    Cputime(t);
    L := Relative_extension_creation(ground_field, extension);
    print rank;
    V1 := []; V2 := []; V3 := [];
    for i in [1..rank] do
	Append(~V1, Relative_exponentiation(W1, [K[i,j] : j in [1..r]], ground_field, extension:KE:=L));
	Append(~V2, ElementToSequence( (&+ [ (K[i, j])* Vector(W2[j]) : j in [1..r] ]) ) );
    end for;
    delete L;
    W := [];
    time_cube_kernel := Cputime(t);
    time_cube_root := 0;
    NORMS1 := [];
    X := [ [V1[i], V2[i] ] : i in [1..rank]];
    print "starting the reduction in Log";
    X := Relative_power_Logreduction(X, U, ground_field, extension, extension[2]);
    Sort_Vectornorm(~X);
    V1 := [X[i,1] : i in [1..#X]];
    V3 := [ElementToSequence(Vector(X[i,2])/extension[2]) : i in [1..#X]];
    return [[V1[i], V3[i]] : i in [1..#V1]];
end function;



/* Compute a generating family of the units defined by  */
/* and controlled by d given the subgroup U such that */
/* OK^p < U < OK ; precision in Log is l */
/* cube roots are computed with real lattice */
Relative_subgroup_from_power_real := function(U, U_pow, ground_field, extension, exponent, precision_log: precision := 1, basis_lattice := 1, unitary := 1, depth:=1, red_version:="lll")
    sub_ext := <extension[1][1..#extension[1]-depth], extension[2]>;
    if precision eq 1 then
	prec := 1;
	real_lattice, uni := Relative_real_basis_lattice_init(ground_field, sub_ext);
    else
	prec := precision;
	real_lattice := basis_lattice;
	uni := unitary;
    end if;
    Sort_Vectornorm(~U_pow);
    V1 := [U_pow[i,1] : i in [1..#U_pow]];
    V1, prec, real_lattice, uni := Relative_real_root_family_depth(V1, ground_field, extension, exponent:depth:=depth, precision:=prec, basis_lattice:=real_lattice, unitary:=uni);
    U_pow := [[V1[i], U_pow[i,2]] : i in [1..#V1]];
    U := Family_purge(U cat U_pow, Relative_extension_dimension(ground_field, extension)[1]);
    U := Relative_family_reduction(U cat U_pow, ground_field, extension, precision_log: version:=red_version);
    return U, prec, real_lattice, uni;
end function;


// compute units of MCF(e) controlled by d with real method for cube roots
KF_units_real := function(field_sequence, field_exponent, precision_log, bool: Units_List := [* [* *], [* *] *], grh := true, red_version:="lll")
    Units_List := Units_List;
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    list_primes := List_primes(field_sequence);
    field_basis_free := KF_primefree_basis(field_sequence, field_exponent:list_primes := list_primes);
    cube_roots_number := 0;
    t := Cputime();
    s := Cputime();
    INDEX := Index(Units_List[1], field_sequence);
    precision := 1; uni:=1; lattice:=1;
    if INDEX ne 0 then //test if KF is in the list already calculated
	return Units_List[2][INDEX], Units_List, 0, 0;
	print Cputime(s);
    else
	if (field_length eq 0) then
	    return [];
	elif (field_length eq 1) then      // if KF is a minimal field, calculate the unit group with standard method
	    F := KF_creation(field_sequence, field_exponent:Check:=false);
	    time G, M := UnitGroup(F:GRH:=grh);
	    gen := Generators(G);
	    units := [];
	    for k in [2..#gen] do
		u := NFelement_to_vector1((F!M(G.k)), field_sequence, field_exponent);
		w := KF_Log_embedding(u, field_sequence, field_exponent, precision_log: basis:=field_basis_free, list_primes:=list_primes);
		Append(~units, [u, w]);
	    end for;
	    Append(~Units_List[1], field_sequence);
	    Append(~Units_List[2], units);
	    delete gen, F, G, M;
	    return units, Units_List, 0, 0;
	else
	    s := Cputime();
	    print "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
	    print " Starting to compute the units of the field defined by", field_sequence, "\n";
	    // define the sequences of the four subfields
	    T := [RationalField() !1];
	    Tminus := [-1];
	    Z := ZeroSequence(RationalField(), field_dim-1);
	    T := T cat Z;
	    Tminus := Tminus cat Z;
	    ms := field_sequence[field_length-1];
	    mt := field_sequence[field_length];
	    m_0 := Prune(Prune(field_sequence));	
	    // Compute the units of the chosen subfields";
	    s := Cputime();
	    subfield_sequence := m_0 cat [ms];
	    subfield_basis_free := KF_primefree_basis(subfield_sequence, field_exponent: list_primes := list_primes);
	    U, Units_List := $$(subfield_sequence, field_exponent, precision_log, bool:Units_List:=Units_List, red_version:=red_version);
	    "units computed in ", Cputime(s);
	    U := Complete_extension(U, subfield_sequence, subfield_basis_free, field_sequence, field_basis_free, field_exponent: list_primes:=list_primes);
	    "embedding computed in", Cputime(s);
	    for j in [0..field_exponent-1] do
		"****************************************";
		subfield_sequence := m_0 cat [ms^j*mt]; /* defines subfield */
		V, Units_List := $$(subfield_sequence, field_exponent, precision_log, bool:Units_List:=Units_List, red_version:= red_version); /* recursive call to compute units of subfield */
		"units of ", j+2," th subfield computed in ", Cputime(s);
		subfield_basis_free := KF_primefree_basis(subfield_sequence, field_exponent: list_primes := list_primes); /* computes basis of subfield */
		V := Complete_extension(V, subfield_sequence, subfield_basis_free, field_sequence, field_basis_free, field_exponent: list_primes:=list_primes);

		for i in [1..#V] do 	
		    Include(~U, V[i]);
		end for;
		delete V;
	
		U := Family_purge(U, field_dim);
		print "purge done";
		U := SetToSequence(SequenceToSet(Family_reduction(U, field_sequence, field_exponent, precision_log: version:=red_version)));
		U := SetToSequence(SequenceToSet(Family_reduction(U, field_sequence, field_exponent, precision_log)));

		U := Family_purge(U, field_dim);
		print "purge done";
		
		if field_exponent eq 2 then
		    Append(~U, [Tminus, [0] cat Z]);
		end if;

		
	    end for;

	    U := Family_purge(U, field_dim);
	    if field_exponent eq 2 then
		Append(~U, [Tminus, [0] cat Z]);
	    end if;

	    U, precision, lattice, uni, rank := Subgroup_from_power_real(U, field_sequence, field_exponent, field_basis_free, precision_log, bool: red_version:=red_version);
	    U := SetToSequence(SequenceToSet(Family_reduction(U, field_sequence, field_exponent, precision_log: version:=red_version)));
	    U := SetToSequence(SequenceToSet(Family_reduction(U, field_sequence, field_exponent, precision_log)));

	    
	    U := Family_purge(U, field_dim);
	    print "purge done";

	    V := []; 			/* will reduce new family */
	    kmc := Cputime();
	    for i in [1..#U] do
		Append(~V, U[i]);
		if ((U[i,1] eq T) or (U[i,1] eq Tminus)) then
		    Prune(~V);
		end if;
	    end for;

	    time_final_reduction := Cputime(kmc);

	    V := Family_purge(U, field_dim);
	    UNITS := V;
	    Append(~Units_List[1], field_sequence);
	    Append(~Units_List[2], UNITS);
	    delete U, V;
	    return UNITS, Units_List, precision, lattice, uni;
	end if;
    end if;
end function;


Simple_relative_units_real := function(ground_field, extension, precision_log : Units_list := [* [* *], [* *] *], depth:=1, grh:=true, red_version:="lll")
    a := KF_is_simple(ground_field);
    b := KF_is_simple(extension);
    field_dim := Relative_extension_dimension(ground_field, extension)[1];
    T := [0 : i in [1..field_dim]];
    Tminus := [-1] cat ZeroSequence(RationalField(), field_dim-1);
    T_ONE := [Tminus, T];
    print [ground_field, extension];
    if (a and b) then
	F := Relative_extension_creation(ground_field, extension);
	F1 := KF_creation([ground_field[1,1]^extension[2]*extension[1,1]^ground_field[2]], ground_field[2]*extension[2]);
	bool := IsIsomorphic(F, F1);
	time G, M := UnitGroup(F1:GRH:=grh);
	gen := Generators(G);
	units := [];
	for k in [2..#gen] do
	    u := Relative_NFelement_to_vector1(F!(F1!M(G.k)), ground_field, extension);
	    w := Relative_Log_embedding(u, ground_field, extension, precision_log);
	    Append(~units, [u, w]);
	end for;
	Append(~units, T_ONE);
	Append(~Units_list[1], [ground_field, extension]);
	Append(~Units_list[2], units);
	delete gen, F, G, M;
	return units, Units_list, 0, 0;
    elif (a and (not b)) then
	/* define first subextension */
	ms := extension[1][#extension[1]-1];
	mt := extension[1][#extension[1]];
	m_0 := Prune(Prune(extension[1]));
	subext := <m_0 cat [ms], extension[2]>;
	"Compute first subextension";
	U, Units_list := $$(ground_field, subext, precision_log:Units_list:=Units_list, depth:=Max(depth-1, 1));
	// purge
	U := Family_purge(U, Relative_extension_dimension(ground_field, subext)[1]);
	// extend
	U := Relative_complete_extension(U, ground_field, subext, extension);
	for j in [0..extension[2]-1] do
	    /* define subextension */
	    subext := <m_0 cat [ms^j*mt], extension[2]>;
	    "recursive call to compute units of subextension";
	    V, Units_list := $$(ground_field, subext, precision_log: Units_list:=Units_list, depth:=Max(depth-1, 1), red_version := red_version); 
	    // purge
	    V := Family_purge(V, Relative_extension_dimension(ground_field, subext)[1]);
	    "extend to extension";
	    V := Relative_complete_extension(V, ground_field, subext, extension);
	    /* add elements of subfield to family already calculated */
	    for i in [1..#V] do 
		Include(~U, V[i]);
	    end for;
	    delete V;
	    /* purge */
	    U := Family_purge(U, Relative_extension_dimension(ground_field, extension)[1]);
	    /* reduces in log */
	    U := Relative_family_reduction(U, ground_field, extension, precision_log: version:=red_version);
	    U := Relative_family_reduction(U, ground_field, extension, precision_log);
	    /* purge */
	    U := Family_purge(U, Relative_extension_dimension(ground_field, extension)[1]);
	end for;
	Include(~U, T_ONE);
	/* detect powers */
	U_pow := Relative_detect_powers(U, ground_field, extension);
	/* compute roots */
	a1, d_t := Relative_depth(ground_field, extension);
	if a1 eq 1 then
	    U, precision, real_lattice, uni := Relative_subgroup_from_power_real(U, U_pow, ground_field, extension, extension[2], precision_log:depth:=d_t);
	elif a1 eq 0 then
  	    U_s := Relative_swap_field_rep_family(U, ground_field, extension: size:=2);
	    Upow_s := Relative_swap_field_rep_family(U_pow, ground_field, extension: size:=2);
	    U, precision, real_lattice, uni := Relative_subgroup_from_power_real(U_s, Upow_s, extension, ground_field, extension[2], precision_log:depth:=d_t);
	    U := Relative_swap_field_rep_family(U, extension, ground_field: size:=2);
	    delete U_s, Upow_s;
	end if;
	/* purge */
	U := Family_purge(U, Relative_extension_dimension(ground_field, extension)[1]);
	/* reduction in log */
	U := Relative_family_reduction(U, ground_field, extension, precision_log: version:=red_version);
	U := Relative_family_reduction(U, ground_field, extension, precision_log);
	/* purge */
	U := Family_purge(U, Relative_extension_dimension(ground_field, extension)[1]);
	U := Relative_family_reduction(U, ground_field, extension, precision_log);
	/* purge */
	U := Family_purge(U, Relative_extension_dimension(ground_field, extension)[1]);
	Include(~U, T_ONE);
	Append(~Units_list[1], [ground_field, extension]);
	Append(~Units_list[2], U);
	return U, Units_list, precision, real_lattice, uni;
    elif (not a) and b then
	ground1 := extension;
	ext1 := ground_field;
	U, Units_list, precision, real_lattice, uni := $$(ground1, ext1, precision_log:Units_list:=Units_list, red_version:=red_version);
	U := Relative_swap_field_rep_family(U, ground1, ext1:size:=2);
	Include(~U, T_ONE);
	return U, Units_list, precision, real_lattice, uni;
    end if;
    return false;
end function;


Relative_units_real := function(ground_field, extension, precision_log : Units_list:= [* [* *], [* *] *], depth:=1, grh:=true, red_version:="lll")
    a := KF_is_simple(ground_field);
    b := KF_is_simple(extension);
    field_dim := Relative_extension_dimension(ground_field, extension)[1];
    T := [0 : i in [1..field_dim]];
    Tminus := [-1] cat ZeroSequence(RationalField(), field_dim-1);
    T_ONE := [Tminus, T];
    print [ground_field, extension];
    if a or b then
	return Simple_relative_units_real(ground_field, extension, precision_log:Units_list:=Units_list, depth:=depth, grh:=grh);
    else
	ms := extension[1][#extension[1]-1];
	mt := extension[1][#extension[1]];
	m_0 := Prune(Prune(extension[1]));
	subext := <m_0 cat [ms], extension[2]>;
	"Compute first subextension";
	U, Units_list := $$(ground_field, subext, precision_log:Units_list:=Units_list, depth:=Max(1, depth-1), grh:=grh);
	// purge
	U := Family_purge(U, Relative_extension_dimension(ground_field, subext)[1]);
	// extend
	U := Relative_complete_extension(U, ground_field, subext, extension);
	for j in [0..extension[2]-1] do
	    /* define subextension */
	    subext := <m_0 cat [ms^j*mt], extension[2]>;
	    "recursive call to compute units of subextension";
	    V, Units_list := $$(ground_field, subext, precision_log: Units_list:=Units_list, depth:=Max(1, depth-1), grh:=grh, red_version:=red_version); 
	    // purge
	    V := Family_purge(V, Relative_extension_dimension(ground_field, subext)[1]);
	    "extend to extension";
	    V := Relative_complete_extension(V, ground_field, subext, extension);
	    /* add elements of subfield to family already calculated */
	    for i in [1..#V] do 
		Include(~U, V[i]);
	    end for;
	    delete V;
	    /* purge */
	    U := Family_purge(U, Relative_extension_dimension(ground_field, extension)[1]);
	    /* reduces in log */
	    U := Relative_family_reduction(U, ground_field, extension, precision_log: version:=red_version);
	    U := Relative_family_reduction(U, ground_field, extension, precision_log);
	    /* purge */
	    U := Family_purge(U, Relative_extension_dimension(ground_field, extension)[1]);
	end for;
	Include(~U, T_ONE);
	/* detect powers */
	U_pow := Relative_detect_powers(U, ground_field, extension);
	/* compute roots */
	a1, d_t := Relative_depth(ground_field, extension);
	if a1 eq 1 then
	    U, precision, real_lattice, uni := Relative_subgroup_from_power_real(U, U_pow, ground_field, extension, extension[2], precision_log:depth:=d_t);
	elif a1 eq 0 then
  	    U_s := Relative_swap_field_rep_family(U, ground_field, extension: size:=2);
	    Upow_s := Relative_swap_field_rep_family(U_pow, ground_field, extension: size:=2);
	    U, precision, real_lattice, uni := Relative_subgroup_from_power_real(U_s, Upow_s, extension, ground_field, extension[2], precision_log:depth:=d_t);
	    U := Relative_swap_field_rep_family(U, extension, ground_field: size:=2);
	    delete U_s, Upow_s;
	end if;

	U := Family_purge(U, Relative_extension_dimension(ground_field, extension)[1]);
	/* reduction in log */
	U := Relative_family_reduction(U, ground_field, extension, precision_log: version:=red_version);
	/* purge */
	U := Family_purge(U, Relative_extension_dimension(ground_field, extension)[1]);
	/* reduction in log */
	U := Relative_family_reduction(U, ground_field, extension, precision_log);
	/* purge */
	U := Family_purge(U, Relative_extension_dimension(ground_field, extension)[1]);
	Append(~Units_list[1], [ground_field, extension]);
	Append(~Units_list[2], U);
	return U, Units_list, precision, real_lattice, uni;
    end if;
end function;


/* ######################################################################################### */
/* ######################################################################################### */
/* ######################################################################################### */
/* ######################################################################################### */


KF_simple_units := function(field_sequence, field_exponent, precision_log: Units_List := [* [* *], [* *] *], grh := true, field_list:=[], reg:=1)
    Units_List := Units_List;
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    list_primes := List_primes(field_sequence);
    field_basis_free := KF_primefree_basis(field_sequence, field_exponent:list_primes := list_primes);
    INDEX := Index(Units_List[1], field_sequence);
    Reg:=reg;
    if INDEX ne 0 then   //test if KF is in the list already calculated
	return Units_List[2][INDEX], Units_List, Reg, 0;
    else
	if (field_length eq 0) then
	    return [];
	elif (field_length eq 1) then      // if KF is a minimal field, calculate the unit group with standard method
	    time F := KF_creation(field_sequence, field_exponent:Check:=false);
	    time G, M := UnitGroup(F: GRH:=grh);
	    gen := Generators(G);
	    units := [];
	    for k in [2..#gen] do
		u := NFelement_to_vector1((F!M(G.k)), field_sequence, field_exponent);
		w := KF_Log_embedding(u, field_sequence, field_exponent, precision_log: basis:=field_basis_free, list_primes:=list_primes);
		Append(~units, [u, w]);
	    end for;
	    Append(~Units_List[1], field_sequence);
	    Append(~Units_List[2], units);
	    delete gen, F, G, M;
	    Reg *:= Determinant(LogLattice_creation(units));
	    return units, Units_List, Reg;
	else
	    ms := field_sequence[field_length-1];
	    mt := field_sequence[field_length];
	    m_0 := Prune(Prune(field_sequence));	
	    // Compute the units of the chosen subfields";
	    s := Cputime();
	    subfield_sequence := m_0 cat [ms];
	    time subfield_basis_free := KF_primefree_basis(subfield_sequence, field_exponent: list_primes := list_primes);
	    time U, Units_List, Reg := $$(subfield_sequence, field_exponent, precision_log:Units_List:=Units_List, reg:=Reg);
	    "units computed in ", Cputime(s);
	    U := Complete_extension(U, subfield_sequence, subfield_basis_free, field_sequence, field_basis_free, field_exponent: list_primes:=list_primes);
	    "embedding computed in", Cputime(s);
	    for j in [0..field_exponent-1] do
		"****************************************";
		subfield_sequence := m_0 cat [ms^j*mt]; /* defines subfield */
		V, Units_List, Reg := $$(subfield_sequence, field_exponent, precision_log:Units_List:=Units_List, reg:=Reg); /* recursive call to compute units of subfield */
		"units of ", j+2," th subfield computed in ", Cputime(s);
		subfield_basis_free := KF_primefree_basis(subfield_sequence, field_exponent: list_primes := list_primes); /* computes basis of subfield */
		time V := Complete_extension(V, subfield_sequence, subfield_basis_free, field_sequence, field_basis_free, field_exponent: list_primes:=list_primes);
		for i in [1..#V] do 	/* add elements of subfield to list of elements in the field */
		    Include(~U, V[i]);
		end for;
		delete V;
		delete subfield_sequence;
		delete subfield_basis_free;
	    end for;
	    Append(~Units_List[1], field_sequence);
	    Append(~Units_List[2], U);
	    return U, Units_List, Reg;
	end if;
    end if;
end function;

