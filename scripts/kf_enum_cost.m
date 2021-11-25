load "../src/start_file.m";
Pol_ring<x> := PolynomialRing(Integers());
SetClassGroupBounds("GRH");
RR := RealField(5);

SIZE_KEYS:=0;

GRH_BOOL := true;

field_dim := FIELD_EXP^LENGTH;


file_data_key_lll := "../data_kf/key_enum_" cat IntegerToString(FIELD_EXP) cat "_" cat IntegerToString(LENGTH) cat "_" cat "lll";
file_data_key_bkz := "../data_kf/key_enum_" cat IntegerToString(FIELD_EXP) cat "_" cat IntegerToString(LENGTH) cat "_" cat "bkz";

file_data_basis_lll := "../data_kf/basis_enum_" cat IntegerToString(FIELD_EXP) cat "_" cat IntegerToString(LENGTH) cat "_" cat "lll";
file_data_basis_bkz := "../data_kf/basis_enum_" cat IntegerToString(FIELD_EXP) cat "_" cat IntegerToString(LENGTH) cat "_"cat "bkz";

file_key_stats := "../data_kf/key_stats_" cat IntegerToString(FIELD_EXP) cat "_" cat IntegerToString(LENGTH);



if field_dim lt 400 then
    
    for q in PRIMES do
	print "***********************************";
	print "field with ", q, " as first prime";
	d := [q];
	while #d lt LENGTH do
	    Append(~d, NextPrime(d[#d]));
	end while;
	

	kf := <d, FIELD_EXP>;

	/* defining files names */
	file_end_lll := (&cat ["_" cat IntegerToString(d[i]) : i in [1..#d]]) cat "__" cat IntegerToString(FIELD_EXP) cat "_" cat "lll";
	file_end_bkz := (&cat ["_" cat IntegerToString(d[i]) : i in [1..#d]]) cat "__" cat IntegerToString(FIELD_EXP) cat "_" cat "bkz";
	file_units_lll := "../data_kf/UNITS/units" cat file_end_lll;
	file_units_bkz := "../data_kf/UNITS/units" cat file_end_bkz;

	
	/* generating keys and keeping norms of p_H(Log (g)) */
	stats_norm := KF_stat_log_norm_key(<d, FIELD_EXP>, SIZE_KEYS, 500: size_set:=500);

	r1, r2 := KF_signature(kf);
	rank := r1+r2-1;
	
	/* evaluating enum costs */

	/* first lll-reduced basis */
	s := Read(file_units_lll);
	L := eval s;
	U := L[1];
	LU := Matrix([U[i, 2] : i in [1..#U]]);
	LU := RowSubmatrixRange(LLL(LU: Delta:=0.99), 1, Rank(LU));
	RU := RealField(15)! ( Sqrt(Determinant(ChangeRing(LU*Transpose(LU), RealField(500)))));
	precision_log := L[6];
	latt := Lattice(LU);
	/* RU := RealField(15)!Sqrt(Determinant(latt)); */
	scaled_vol := Exp(Log(RU)/rank);
	delete L;
	
	
	enum_basis_lll :=  [Log(2, EnumerationCost(latt, scaled_vol^2)), Log(2, EnumerationCost(latt, (rank/(2*Pi(RealField())*Exp(1)))*scaled_vol^2)) ];
	enum_key_lll := [EnumerationCost(latt, RealField(100)!stats_norm[i]) : i in [1..#stats_norm]];
	
	enum_key_lll := [Log(2, enum_key_lll[i]) : i in [1..#stats_norm]];

	
	/* now bkz-reduced basis */
	s := Read(file_units_bkz);
	L := eval s;
	U := L[1];
	LU := Matrix([U[i, 2] : i in [1..#U]]);
	LU := RowSubmatrixRange(LLL(LU: Delta:=0.99), 1, Rank(LU));
	precision_log := L[6];
	latt := Lattice(LU);
	delete L;

	enum_basis_bkz :=  [Log(2, EnumerationCost(latt, scaled_vol^2)), Log(2, EnumerationCost(latt, (rank/(2*Pi(RealField())*Exp(1)))*scaled_vol^2)) ];
	enum_key_bkz := [Log(2, EnumerationCost(latt, RealField(100)!stats_norm[i])) : i in [1..#stats_norm]];
	
	delete U, LU, latt;
	       

	/* print everything */

	/* first key stats + vol reduced */
	FILE := Open(file_key_stats, "a");
	for p in d do
	    fprintf FILE, "%o\t", p;
	end for;
	
	fprintf FILE, "%o\t", RR!scaled_vol;
	
	fprintf FILE, "%o\t%o\t%o\t%o\t%o\n", RR!Sqrt(stats_norm[1]) , RR!Sqrt(stats_norm[2]), RR!Sqrt(stats_norm[3]), RR!Sqrt(stats_norm[4]), RR!Sqrt(stats_norm[5]);
	delete FILE;
	
	/* lll basis + keys */
	FILE := Open(file_data_key_lll, "a");
	for p in d do
	    fprintf FILE, "%o\t", p;
	end for;
	fprintf FILE, "%o\t", RR!scaled_vol;
	fprintf FILE, "%o\t%o\t%o\t%o\t%o\n", RR!enum_key_lll[1] , RR!(enum_key_lll[2]), RR!(enum_key_lll[3]), RR!(enum_key_lll[4]), RR!enum_key_lll[5];
	delete FILE;
	
	FILE := Open(file_data_basis_lll, "a");
	for p in d do
	    fprintf FILE, "%o\t", p;
	end for;
	fprintf FILE, "%o\t", RR!scaled_vol;
	fprintf FILE, "%o\t%o\n", RR!enum_basis_lll[1] , RR!(enum_basis_lll[2]);
	delete FILE;

	
	/* bkz basis + keys */
	FILE := Open(file_data_key_bkz, "a");
	for p in d do
	    fprintf FILE, "%o\t", p;
	end for;
	fprintf FILE, "%o\t", RR!scaled_vol;
	fprintf FILE, "%o\t%o\t%o\t%o\t%o\n", RR!enum_key_bkz[1] , RR!(enum_key_bkz[2]), RR!(enum_key_bkz[3]), RR!(enum_key_bkz[4]), RR!enum_key_bkz[5];
	delete FILE;
	
	FILE := Open(file_data_basis_bkz, "a");
	for p in d do
	    fprintf FILE, "%o\t", p;
	end for;
	fprintf FILE, "%o\t", RR!scaled_vol;
	fprintf FILE, "%o\t%o\n", RR!enum_basis_bkz[1] , RR!(enum_basis_bkz[2]);
	delete FILE;

	
    end for;
end if;

exit;
