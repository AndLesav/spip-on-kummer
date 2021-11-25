MyLogEmbedding_from_KF := function(lx)
    l := ChangeUniverse(lx, RealField());
    for i in [2..#l] do
	l[i] := Sqrt(2)*l[i];
    end for;
    return l;
end function;


MyLogEmbedding := function(x, K: prec:=200, lx:=[], sign := [], field_type:="")
    if #lx eq 0 then
	l := Logs(K!x: Precision:=prec);
	if #sign ne 0 then
	    r1 := sign[1];
	    r2 := sign[2];
	else
	    r1, r2 := Signature(K);
	end if;
	L := [Round((2^prec)*l[i])/2^prec : i in [1..r1]] cat [2*Round((2^prec)*l[i])/2^prec : i in [r1+1..r1+r2]];
    else
	L := lx;
    end if;
    if field_type eq "kum" then
	L := MyLogEmbedding_from_KF(L);
    end if;
    return L;
end function;


MyFlatLogEmbedding := function(x, K: prec:=200, lx:=[], sign := [], field_type:="")
    if #lx eq 0 then
	l := Logs(K!x: Precision:=prec);
	if #sign ne 0 then
	    r1 := sign[1];
	    r2 := sign[2];
	else
	    r1, r2 := Signature(K);
	end if;
	L := [Round((2^prec)*l[i])/2^prec : i in [1..r1]] cat [Round((2^prec)*l[i])/2^prec : i in [r1+1..r1+r2]] cat [Round((2^prec)*l[i])/2^prec : i in [r1+1..r1+r2]];;
    else
	L := lx;
    end if;
    return L;
end function;


My_proj_norm := function(lg, rank: type:="")
    L := lg;
    if type eq "flat" then
	n := #lg;
	m := (&+ L) / (n);
    else
	m := (&+ L) / (rank+1);
    end if;
    L := [L[i]-m : i in [1..#L]];
    return Sqrt(Norm(Vector(L)));
end function;


MyEnumerationCost := function(L, B: Prune:=[])
    return EnumerationCost(Lattice(Matrix(L)), B);
end function;


MyRegulator := function(LU)
    return Sqrt(Determinant(Lattice(RemoveColumn(Matrix(LU), 1))));
end function;


LogLattice_from_units := function(U, K: prec:=200, type:="")
    L := [];
    for i in [1..#U] do
	a := U[i];
	if type eq "flat" then
	    l := MyFlatLogEmbedding(a, K: prec:=prec);    
	else
	    l := MyLogEmbedding(a, K: prec:=prec);
	end if;
	Append(~L, l);
    end for;
    L := LLL(Matrix(L));
    L := [Eltseq(L[i]) : i in [1..Nrows(L)]];
    return L;
end function;


LogUnit_lattice := function(K: prec:=200, type:="")
    G, m := UnitGroup(K: GRH:=true);
    gen1 := Generators(G);
    gen := [K!m(G.i) : i in [2..#gen1]];
    L := [];
    return LogLattice_from_units(gen, K: prec:=prec, type:=type);
end function;


/* m is a prime power */
MyCyclotomic_units_log := function(n, K: prec:=200, type:="")
    zeta := K.1;
    m := Degree(K);
    U := [];
    for i in [2..(m+1)] do
	if GCD(i, n) eq 1 then
	    u := (zeta^i-1);
	    /* v := (zeta^(-i)-1)/(zeta-1); */
	    Append(~U, u);
	    /* Append(~U, v); */
	end if;
    end for;
    L := [];
    if type eq "flat" then
	ld := MyFlatLogEmbedding(zeta-1, K: prec:=prec);
    else
	ld := MyLogEmbedding(zeta-1, K: prec:=prec);
    end if;
    for i in [1..#U] do
	if type eq "flat" then
	    ln := MyFlatLogEmbedding(U[i], K: prec:=prec);
	else
	    ln := MyLogEmbedding(U[i], K: prec:=prec);
	end if;
	Append(~L, Eltseq(Vector(ln)-Vector(ld)));			  
    end for;
    L := LLL(Matrix(L));
    L := [Eltseq(L[i]) : i in [1..Rank(L)]];
    return L;
end function;


/* Reduction of h in Log-unit Lattice U */
My_RedGen_log := function(Lh, LU, K: red_method:="babai", prune:=[])
    Mu := LU;
    Mu := Matrix(Mu);
    h2 := Lh;
    ONE := [Rationals()!1 : i in [1..#h2]];
    h3 := Orthogonal_projection(h2, ONE);
    if red_method eq "babai" then
	Lh_red, relations := Babai_decoding(Mu, h2);
    elif red_method eq "cvp" then
	Lu := Lattice(Mu);
	CV := ClosestVectors(Lu, Vector(h3))[1];
	d := Denominator(Mu);
	relations := ChangeUniverse(ElementToSequence(-Solution(ChangeRing(d*Mu, Integers()), ChangeRing(d*CV, Integers()))), Integers()) cat [1];
	Lh_red := ElementToSequence(Vector(h2) - CV);
    else
	print "ERROR: WRONG METHOD NAME GIVEN";
	return false;
	exit;
    end if;
    return Lh_red;
end function;


Stat_log_norm_key := function(K, size_key, precision: size_set:=200, LU:=[], pruning:=false, p:=1/2, n:=10, shape:="uni", supp:=1, file:="")
    dim := AbsoluteDegree(K);
    r1, r2 := Signature(K);
    rank := r1+r2-1;
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
	g := Keygen(size_key, dim: shape:=shape, p:=p, n:=n, length_supp:=supp, kum_field:=K);
	Lg := MyLogEmbedding(K!g, K :prec:=precision);
	n_g := RealField(10)!Norm(Vector(Orthogonal_projection(Lg, [Rationals()!1 : j in [1..#Lg]])));
	if n_g ne 0 then
	    Append(~norms, n_g);
	    if (LU ne []) and (#file ne 0) then
		e := MyEnumerationCost(LU, RealField()!n_g: Prune:=prune);
		FILE := Open(file, "a");
		fprintf FILE, "%o\n", e;
		delete FILE;
	    end if;
	end if;
    end while;
    Sort(~norms);
    if LU ne [] then
	mi +:= MyEnumerationCost(LU, RealField()!norms[1]);
	ma +:= MyEnumerationCost(LU, RealField()!norms[#norms]);
	q1 := MyEnumerationCost(LU, RealField()!norms[rq]);
	me := MyEnumerationCost(LU, RealField()!norms[rm]);
	q3 := MyEnumerationCost(LU, RealField()!norms[rq+rm]);
    end if;
    stats := [mi, q1, me, q3, ma];
    return stats;
end function;


Stats_decode := function(K, LU, size_key, precision: size_set:=200, pruning:=false, p:=1/2, n:=10, shape:="uni", supp:=1, file:="")
    dim := AbsoluteDegree(K);
    r1, r2 := Signature(AbsoluteField(K));
    rank := r1+r2-1;
    count := 0;
    prune:= [];
    if pruning then
	prune := [RealField()!(rank-i+1)/rank : i in [1..rank]];
    end if;
    for i in [1..size_set] do
	if i mod 10 eq 0 then
    	    printf "%o, %o \n", i, RealField(3)!count/(i-1);
	end if;
	g := Keygen(size_key, dim: shape:=shape, p:=p, n:=n, length_supp:=supp, kum_field:=K);
	Lg := MyLogEmbedding(g, K :prec:=precision);
	Lh := RandomGenLog(Lg, LU, precision, K: size:=20);
	Lh_red := My_RedGen_log(Lh, LU, K);
	if Lg eq Lh_red then
	    count +:=1;
	end if;
    end for;
    return count;
end function;


Stats_log_norm_proj := function(K, size_key, precision, volume: type_log := "", size_set:=200, p:=1/2, n:=10, shape:="uni", supp:=1, file:="")
    dim := AbsoluteDegree(K);
    r1, r2 := Signature(AbsoluteField(K));
    rank := r1+r2-1;
    scaled_vol := Root(volume, rank);
    stats := [];
    mi := 0;
    ma := 0;
    q1 := 0;
    q3 := 0;
    me := 0;
    norms := [];
    ec := [];
    i := 0;
    while #norms lt size_set do
	i := #norms;
	if i mod 50 eq 0 then print i; end if;
	g := Keygen(size_key, dim: shape:=shape, p:=p, n:=n, length_supp:=supp, kum_field:=K);
	if type_log eq "flat" then
	    Lg := MyFlatLogEmbedding(g, K: prec:=precision, sign:=[r1, r2]);
	else
	    Lg := MyLogEmbedding(g, K: prec:=precision, sign:=[r1, r2]);
	end if;
	n_g := My_proj_norm(Lg, rank: type := type_log)/scaled_vol;
	if n_g ne 0 then
	    Append(~norms, n_g);
	    if (#file ne 0) then
		FILE := Open(file, "a");
		fprintf FILE, "%o\n", n_g;
		delete FILE;
	    end if;
	end if;
    end while;
    Sort(~norms);
    rq := #norms div 4;
    rm := #norms div 2;
    mi := RealField()!norms[1];
    ma := RealField()!norms[#norms];
    q1 := RealField()!norms[rq];
    me := RealField()!norms[rm];
    q3 := RealField()!norms[rq+rm];
    stats := [mi, q1, me, q3, ma];
    return stats;
end function;



Stats_log_norm_proj_kummer := function(K, size_key, precision, volume: size_set:=200, p:=1/2, n:=10, shape:="uni", supp:=1, file:="", type_log := "")
    dim := KF_dimension(K);
    if K[2] eq 2 then
	r1 := dim;
	r2 := 0;
	rank := r1+r2-1;
    else
	r1 := 1;
	r2 := (dim-1) div 2;
	rank := r1+r2-1;
    end if;
    scaled_vol := Root(volume, rank);
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
    i := 0;
    while #norms lt size_set do
	i := #norms;
	if i mod 50 eq 0 then print i; end if;
	g := Keygen(size_key, dim: shape:=shape, p:=p, n:=n, length_supp:=supp, kum_field:=K);
	Lg := ChangeUniverse(KF_Log_embedding(g, K[1], K[2], precision), RealField(precision));
	if type_log eq "" then
	    list_pairs := List_indexes_conjugates(#K[1], K[2]);
	    Lg := PartLog_from_flat(Lg, list_pairs);
	end if;
	n_g := My_proj_norm(Lg, rank: type:=type_log)/scaled_vol;
	if n_g ne 0 then
	    Append(~norms, n_g);
	    if (#file ne 0) then
		FILE := Open(file, "a");
		fprintf FILE, "%o\n", n_g;
		delete FILE;
	    end if;
	end if;
    end while;
    Sort(~norms);
    mi := RealField()!norms[1];
    ma := RealField()!norms[#norms];
    q1 := RealField()!norms[rq];
    me := RealField()!norms[rm];
    q3 := RealField()!norms[rq+rm];
    stats := [mi, q1, me, q3, ma];
    return stats;
end function;


Stats_log_norm_proj_relative := function(Kg, Ke, size_key, precision, volume: size_set:=200, p:=1/2, n:=10, shape:="uni", supp:=1, file:="", type_log := "")
    dim := Relative_extension_dimension(Kg, Ke)[1];
    r1, r2 := Relative_extension_signature(Kg, Ke);
    rank := r1+r2-1;
    scaled_vol := Root(volume, rank);
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
    i := 0;
    while #norms lt size_set do
	i := #norms;
	if i mod 50 eq 0 then print i; end if;
	g := Keygen(size_key, dim: shape:=shape, p:=p, n:=n, length_supp:=supp);
	Lg := ChangeUniverse(Relative_Log_embedding(g, Kg, Ke, precision), RealField(precision div 3));
	n_g := My_proj_norm(Lg, rank: type:=type_log)/scaled_vol;
	if n_g ne 0 then
	    Append(~norms, n_g);
	    if (#file ne 0) then
		FILE := Open(file, "a");
		fprintf FILE, "%o\n", n_g;
		delete FILE;
	    end if;
	end if;
    end while;
    Sort(~norms);
    mi := RealField()!norms[1];
    ma := RealField()!norms[#norms];
    q1 := RealField()!norms[rq];
    me := RealField()!norms[rm];
    q3 := RealField()!norms[rq+rm];
    stats := [mi, q1, me, q3, ma];
    return stats;
end function;


My_number_changes := function(M)
    norms := [];
    count := 0;
    for i in [1..Nrows(M)] do
	n := Norm(M[i]);
	if n gt 1 then
	    count +:= 1;
	end if;
    end for;
    return count;
end function;


My_normalize_matrix := function(M)
    L := [];
    for i in [1..Nrows(M)] do
	v := ChangeRing(M[i], RealField());
	v := v/Sqrt(Norm(v));
	Append(~L, Eltseq(v));
    end for;
    return Matrix(L);
end function;


/* compute BKZ and associated data of the lattices such as: */
/* enumeration costs, orthogonality parameters */
My_BKZ := function(N, vol, c)
    r := Rank(N);
    M := IdentityMatrix(RationalField(), r);
    D := Denominator(N);
    N1 := N;
    norms := [];
    count := [];
    enum := [];
    enum_key := [];
    hf := [];
    latt := Lattice(N1);
    scaled_vol := Exp(Log(vol)/r);
    Append(~enum, [Log(2, EnumerationCost(latt, scaled_vol^2)), Log(2, EnumerationCost(latt, (r/(2*Pi(RealField())*Exp(1)))*scaled_vol^2)) ]);

    Append(~enum_key, [Log(2, EnumerationCost(latt, (c[i]*scaled_vol)^2)) : i in [1..#c]]);
    
    d_0, d_n := Orthogonality_parameters(N, 300, r, scaled_vol);
    Append(~hf, [d_0, d_n]);
    
    N1 := Nrows(N)*N1;
    for n in [20..20] do
	N1 := HorizontalJoin(M, N1);
	N1 := BKZ(N1, n: Delta:=0.99);
	N1 := ColumnSubmatrixRange(N1, r+1, Ncols(N1));
	latt := Lattice(ChangeRing(N1, Rationals())/Nrows(N));
	Append(~enum, [Log(2,EnumerationCost(latt, scaled_vol^2)), Log(2, EnumerationCost(latt, (r/(2*Pi(RealField())*Exp(1)))*scaled_vol^2)) ]);
	Append(~enum_key, [Log(2, EnumerationCost(latt, (c[i]*scaled_vol)^2)) : i in [1..#c]]);
	d_0, d_n := Orthogonality_parameters(ChangeRing(N1, Rationals())/Nrows(N), 300, r, scaled_vol);
	Append(~hf, [d_0, d_n]);
    end for;
    return norms, enum, enum_key, hf;
end function;

