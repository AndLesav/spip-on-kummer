integer_valuation := function(D, d)
    e := 0;
    d1 := d;
    while ((D mod d1) eq 0) do
	e := e + 1;
	d1 := d1*d;
    end while;
    return e;
end function;


/* D is an integer, list is a list of integers */
integer_valuation_exponent := function(D, list)
    e := [];
    n := #list;
    for i in [1..n] do
	Append(~e, integer_valuation(D, list[i]));
    end for;
    return e;
end function;


/* D an integer */
prime_valuation_exponent := function(D, list_primes)
    e := [];
    n := #list_primes;
    for i in [1..n] do
	Append(~e, Valuation(D, list_primes[i]));
    end for;
    return e;
end function;


PrimeFreePart := function(D, p: list_primes:=[])
    pf_r := 1;
    pf_q := 1;
    if #list_primes ne 0 then
	exponent := prime_valuation_exponent(D, list_primes);  
	for i in [1..#list_primes] do
	    q, r := Quotrem(exponent[i], p);
	    pf_r := pf_r*list_primes[i]^r;
	    pf_q :=  pf_q*list_primes[i]^q;
	end for;
    else
	facto := Factorisation(D);
	for i in [1..#facto] do
	    q, r := Quotrem(facto[i, 2], p);
	    pf_r := pf_r*facto[i, 1]^r;
    	    pf_q := pf_q*facto[i, 1]^q;
	end for;
    end if;
    return pf_r, pf_q;
end function;


PrimeFreeSequence := function(L, p: list_primes:=[])
    L_r := [];
    L_q := [];
    for i in [1..#L] do
	pf_r, pf_q := PrimeFreePart(L[i], p:list_primes:=list_primes);
	Append(~L_r, pf_r);
	Append(~L_q, pf_q);
    end for;
    return L_r, L_q;
end function;


List_primes := function(sequence)
    list := [];
    for i in [1..#sequence] do
	facto := Factorisation(sequence[i]);
	for j in [1..#facto] do
	    Include(~list, facto[j, 1]);
	end for;
    end for;
    return list;
end function;


stats_seq := function(l)
    Sort(~l);
    stats := [l[1], l[#l div 4], l[#l div 2], l[#l - (#l div 4)], l[#l]];
    return stats, &+l/#l;
end function;


seq_exp := function(v, e)
    w := ZeroSequence(Universe(v), #v);
    for i in [1..#v] do
	w[i] := v[i]^e;
    end for;
    return w;
end function;



/* ######################################################### */
/* ##################   HNF / matrix related ###############  */
/* ######################################################### */

/* Add one vector and calculate HNF */
HNF_addvector := function(H, v)
    R := Min(#v, Nrows(H));
    /* R := #v; */
    Z := ZeroSequence(IntegerRing(), Nrows(H)+1);
    IM := IdentityMatrix(IntegerRing(), Nrows(H)+1);
    M := VerticalJoin(Vector(v), H);
    for i in [1..R] do
	a := M[1, i];
	if a ne 0 then
	    b := M[i+1, i];
	    /* print a, b; */
	    D, U, V := XGCD(a, b);
	    /* print D; */
	    L1 := Z; L2 := Z;
	    L1[1] := b div D; L1[i+1] := - a div D; 
	    L2[1] := U; L2[i+1] := V;
	    L := IM;
	    L[1] := Vector(L1);
	    L[i+1] := Vector(L2);
	    M := L*M;
	    L := IM;
	    for j in [2..i] do
		q := M[j, i] div M[i+1, i];
		M[j] := M[j]- q*M[i+1];
		/* L[j, i+1] := -q; */
	    end for;
	end if;
    end for;
    return Matrix(M[2..(R+1)]);
end function;


/* Add one vector and calculate HNF */
HNF_addvector_classical := function(H, v)
    R := #v;
    H := VerticalJoin(Vector(v), H);
    H := HermiteForm(H: Al:="Classical");
    H := Matrix(H[1..Rank(H)]);
    return H;
end function;


// update HNF with another matrix
HNF_update := function(H, M)
    dH := Denominator(H);
    dM := Denominator(M);
    d := LCM(dH,dM);
    M1 := ChangeRing(d*M, IntegerRing());
    H1 := ChangeRing(d*H, IntegerRing());
    for i in [1..Nrows(M)] do
	H1 := HNF_addvector_classical(H1, ElementToSequence(M1[i]));
    end for;
    return ChangeRing(H1, RationalField())/d;
end function;


// update HNF with another matrix
HNF_update_classical := function(H, M)
    dH := Denominator(H);
    dM := Denominator(M);
    d := LCM(dH,dM);
    M1 := ChangeRing(d*M, IntegerRing());
    H1 := ChangeRing(d*H, IntegerRing());
    for i in [1..Nrows(M)] do
	H1 := HNF_addvector_classical(H1, ElementToSequence(M1[i]));
    end for;
    return ChangeRing(H1, RationalField())/d;
end function;


My_row_maxnorm := function(M)
    norms := [];
    for i in [1..Nrows(M)] do
	Append(~norms, Sqrt(Norm(M[i])));
    end for;
    ma := Max(norms);
    mi := Min(norms);
    Sort(~norms);
    return ma, mi, norms;
end function;


RandomHNF := function(dimension, determinant)
    H := IdentityMatrix(Integers(), dimension);
    H[dimension, dimension] := Random(determinant);
    for i in [1..dimension-1] do
	H[i, dimension] := Random(determinant) mod H[dimension, dimension];
    end for;
    return H;
end function;


/* ######################################################### */
/* #################### LATTICE RELATED #################### */
/* ######################################################### */

/* lambda_1 est */
L1_est := function(vol, rank: est:="gh")
    if est eq "gh" then 
	lambda_1 := Sqrt(rank/(2*Pi(RealField())*Exp(1)))*Root(vol, rank);
    else
	lambda_1 := Root(vol*Gamma(rank/2+1)/(Pi(RealField())^(rank/2)), rank);
    end if;
    return lambda_1;
end function;

/* lattice intersection with Hermite */
Lattice_intersection := function(M1, M2)
    M := HorizontalJoin(M1, M1);
    N := HorizontalJoin(M2, ZeroMatrix(Integers(), Nrows(M2), Ncols(M1)));
    M := VerticalJoin(M, N);
    M := HermiteForm(M: Al:="Classical");
    Z := ZeroMatrix(Integers(), 1, Ncols(M1));
    row_index := Nrows(M)+1;
    test := true;
    while test do
	row_index +:= -1;
	test := ExtractBlock(M, row_index, 1, 1, Ncols(M1)) eq Z;
    end while;
    return ExtractBlock(M, row_index+1, Ncols(M1)+1, Nrows(M)-row_index, Ncols(M1)), ExtractBlock(M, 1, 1, row_index, Ncols(M1));
end function;

/* random element in the same coset modulo lattice L */
RandomCosetRepresentative := function(x, L: size:=5)
    y := Vector(x);    
    for i in [1..#L] do
	/* s := Random(1, size); */
	s := size;
	y +:= Random(Integers(), 2^s)*Vector(L[i]);
    end for;
    return Eltseq(y);
end function;

/* random element in the same coset modulo lattice L */
/* L is given by a matrix */
RandomElement_lattice := function(L: size:=2)
    y := Vector(ZeroSequence(Integers(), Ncols(L)));
    for i in [1..Nrows(L)] do
	y +:= Random(Integers(), 2^size)*L[i];
    end for;
    return Eltseq(y);
end function;


GSO := function(M)
    n := Nrows(M); m := Ncols(M);
    N := M;
    for i in [1..n] do
	for j in [1..i-1] do
            N[i] := N[i] - (InnerProduct(M[i], N[j])/Norm(N[j]))*N[j];
	end for;
    end for;
    return N;
end function;


/* OTHER FUNCTIONS - KUMMER RELATED */

Hermite_factor := function(U, precision_float)
    LU := Matrix([[Round(2^precision_float*U[i,2][j])/(2^precision_float) : j in [1..#U[i,2]]] : i in [1..#U]]);
    R := Rank(LU);
    LU := LLL(LU/* :Delta:=0.999, Eta:=0.500001 */);
    LV := RowSubmatrixRange(LU, 1, Rank(LU));
    LU := ChangeRing(LV, RealField(precision_float));
    det := Sqrt(Determinant(LU*Transpose(LU)));
    hermite_factor := Root(Sqrt(Norm(LU[1]))/Root(det, R), R);
    return RealField(5)!hermite_factor;
end function;


Orthogonality_parameters := function(LU, precision_float, rank, scaled_vol)
    R := rank;
    LU := ChangeRing(LU, RealField(precision_float));
    ma, mi, norms := My_row_maxnorm(LU);
    d_0 := RealField(5)! Exp((Log(mi)-Log(scaled_vol))/rank);
    d_n := RealField(5)! Exp( (&+[Log(norms[i])-Log(scaled_vol) : i in [1..#norms]])/rank);
    return d_0, d_n;
end function;


Latt_basis_stats := function(latt, precision, rank, vol: norms:=[], est := "gh")
    RR := RealField(precision);
    R := rank;
    L := ChangeRing(latt, RR);
    if #norms eq 0 then
	ma, mi, norms := My_row_maxnorm(L);
    end if;
    Sort(~norms);
    if est eq "gh" then 
	lambda_1 := Sqrt(rank/(2*Pi(RR)*Exp(1)))*Root(vol, rank);
    else
	lambda_1 := Root(vol*Gamma(rank/2+1)/(Pi(RR)^(rank/2)), rank);
    end if;
    n_stats, me := stats_seq(norms);
    return [n_stats[i]/lambda_1 : i in [1..#n_stats]], me/lambda_1;
end function;


Sequence_division := function(seq, n)
    if #seq mod n ne 0 then
	print "wrong size: ", n, " does not divide the length of ", seq;
	return false;
	exit;
    else
	l := [];
	q := #seq div n;
	for i in [0..n-1] do
	    Append(~l, seq[1+i*q..(i+1)*q]);
	end for;
    end if;
    return l;
end function;




/* ################################################################ */
/* ################### POLYNOMIAL GENERATIONS ######################*/
/* ############################################################### */


Pol_field_creation_real := function(field_dim, size_coeff)
    p<x> := PolynomialRing(Integers());
    q<y> := PolynomialRing(Integers());
    r1 := 0;
    while r1 eq 0 do
	L_P := [];
	for j in [1..1] do
    	    /* Append(~L_P, x^PRIMES[INDEX]-Random(PRIMES)); */
    	    /* P := x^(2*PRIMES[INDEX])+p![Random(-30, 30) : i in [1..2*PRIMES[INDEX]]]; */
	    P := x^field_dim + p![Random(-10^size_coeff, 10^size_coeff) : i in [1..field_dim]];
    	    while (not IsIrreducible(P)) do
		P := x^field_dim + p![Random(-10^size_coeff, 10^size_coeff) : i in [1..field_dim]];
    		/* P := x^(2*PRIMES[INDEX])+p![Random(-30, 30) : i in [1..2*PRIMES[INDEX]]]; */
    	    end while;
    	    Include(~L_P, P);
	end for;    
	r1 := 0;
	/* K<a> := NumberField(P); */
	K<a> := (AbsoluteField(NumberField(L_P)));
	P := q!DefiningPolynomial(K);
	r1 := Signature(K);
    end while;
    return P;
end function;


Pol_field_creation := function(field_dim, size_coeff: supp :=1)
    p<x> := PolynomialRing(Integers());
    q<y> := PolynomialRing(Integers());
    L_P := [];
    S := SetToSequence(RandomSubset(Set([1..field_dim-1]), Round(supp*(field_dim-1))));
    S := S cat [0];
    /* print S; */
    for j in [1..1] do
	/* Append(~L_P, x^PRIMES[INDEX]-Random(PRIMES)); */
	/* P := x^(2*PRIMES[INDEX])+p![Random(-30, 30) : i in [1..2*PRIMES[INDEX]]]; */
	P := x^field_dim + p!&+[Random(-2^size_coeff, 2^size_coeff)*x^i : i in S];
	while (not IsIrreducible(P)) do
	    P := x^field_dim + p!&+[Random(-10^size_coeff, 10^size_coeff)*x^i : i in S];
	    /* P := x^(2*PRIMES[INDEX])+p![Random(-30, 30) : i in [1..2*PRIMES[INDEX]]]; */
	end while;
	Include(~L_P, P);
    end for;    
    r1 := 0;
    /* K<a> := NumberField(P); */
    K<a> := (AbsoluteField(NumberField(L_P)));
    P := q!DefiningPolynomial(K);
    return P;
end function;    


/* integral polynomial with degree=deg with random coeff in 
                           [-10^size_coeff, 10^size_coeff]  */
Pol_creation_integral := function(deg, size_coeff)
    p<x> := PolynomialRing(Integers());
    return p![Random(-10^size_coeff, 10^size_coeff) : i in [0..deg]];
end function;


/* polynomial of degree deg with coefficients in K
   coefficients are elements in ZZ[K.1]       */
Pol_creation_field := function(K, deg, size_coeff: supp:=[1,1])
    local p, x;
    p<x> := PolynomialRing(K);
    pol := 0;
    S := RandomSubset(Set([0..deg-1]), Round(supp[1]*deg));
    T := RandomSubset(Set([0..Degree(K)-1]), Round(supp[2]*Degree(K)));
    for i in SetToSequence(S) do
	coeff := K!&+[Random(-2^size_coeff, 2^size_coeff)*K.1^j : j in T ];
	pol +:= coeff*x^i;
    end for;
    return pol;
end function;


Pol_field_creation_tower := function(extensions_dim, size_coeff: supp := [1,1,1])
    local p, q, x, y;
    p<x> := PolynomialRing(Integers());
    L := [* Pol_field_creation(extensions_dim[1], size_coeff: supp:=supp[1]) *];
    print "ground field created";
    K := NumberField(L[#L]: Check:=false);
    /* local q, y; */
    q<y> := PolynomialRing(K);
    for i in [2..#extensions_dim] do
	pol := q!Pol_creation_field(K, extensions_dim[i]-1, size_coeff: supp:=supp[2..3]);
	pol +:= y^extensions_dim[i];
	while (not IsIrreducible(q!pol)) do
	    pol := q!Pol_creation_field(K, extensions_dim[i]-1, size_coeff: supp:=supp[2..3]);
	    pol +:= y^extensions_dim[i];
	    /* pol := Pol_field_creation(extensions_dim[i], size_coeff); */
	end while;
	Append(~L, q!pol);
	K := NumberField(L[#L]: Check:=false);
	q<y> := PolynomialRing(K);
    end for;
    return L, K;
end function;


Pol_field_creation_comp := function(extensions_dim, size_coeff: supp := [1 : i in [1..#extensions_dim]])
    local p, q, x, y;
    p<x> := PolynomialRing(Integers());
    L := [Pol_field_creation(extensions_dim[1], size_coeff: supp:=supp[1])];
    print "ground field created";
    K := NumberField(L: Check:=false);
    /* local q, y; */
    q<y> := PolynomialRing(K);
    for i in [2..#extensions_dim] do
	pol := p!Pol_field_creation(extensions_dim[i], size_coeff: supp:=supp[i]);
	/* pol +:= y^extensions_dim[i]; */
	while (not IsIrreducible(p!pol)) do
	    pol := p!Pol_field_creation(extensions_dim[i], size_coeff: supp:=supp[i]);
	end while;
	Append(~L, p!pol);
	K := NumberField(L: Check:=false);
	q<y> := PolynomialRing(K);
    end for;
    return L, K;
end function;


Pol_field_creation_kummer := function(exp, length, range)
    local p, q, x, y;
    p<x> := PolynomialRing(Integers());
    P := PrimesUpTo(range);
    L := [];
    while #L lt length do
	m := Random(P);
	Include(~L, x^exp-m);
    end while;
    K := NumberField(L: Check:=false);
    return L, K;
end function;


Pol_field_creation_tower_real := function(extensions_dim, size_coeff)
    p<x> := PolynomialRing(Integers());
    L := [Pol_field_creation(extensions_dim[1], size_coeff)];
    for i in [2..#extensions_dim] do
	K := NumberField(L: Check:=false);
	q<y> := PolynomialRing(K);
	pol := Pol_field_creation_real(extensions_dim[i], size_coeff);
	while (not IsIrreducible(q!pol)) do
            pol := Pol_field_creation(extensions_dim[i], size_coeff);
	end while;
	Append(~L, p!pol);
    end for;
    K := NumberField(L: Check:=false);
    pol := DefiningPolynomial(AbsoluteField(K));
    return p!pol;
end function;
