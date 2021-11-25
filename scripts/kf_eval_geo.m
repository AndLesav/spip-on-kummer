load "../src/start_file.m";
Pol_ring<x> := PolynomialRing(Integers());
SetClassGroupBounds("GRH");
RR := RealField(5);


GRH_BOOL := true;

field_dim := FIELD_EXP^LENGTH;

if field_dim lt 400 then

    for q in PRIMES do

	print "***********************************";
	print "First prime defining the field: ", q;
	
	d := [q];
	while #d lt LENGTH do
	    Append(~d, NextPrime(d[#d]));
	end while;
	
	kf := <d, FIELD_EXP>;
	
	/* defining files names */
	file_end := (&cat ["_" cat IntegerToString(d[i]) : i in [1..#d]]) cat "__" cat IntegerToString(FIELD_EXP) cat "_" cat RED_VERSION;
	file_units := "../data_kf/UNITS/units" cat file_end;
	file_data := "../data_kf/ortho_param_" cat IntegerToString(FIELD_EXP) cat "_" cat IntegerToString(LENGTH) cat "_" cat RED_VERSION;
	
	s := Read(file_units);
	L := eval s;
	
	U := L[1];
	LU := Matrix([U[i, 2] : i in [1..#U]]);
	precision_log := L[6];
	RU := RealField(15)! ( Sqrt(Determinant(ChangeRing(LU*Transpose(LU), RealField(300)))));

	r1, r2 := KF_signature(<d, FIELD_EXP>);
	rank := r1+r2-1;
	scaled_vol := Exp(Log(RU)/rank);
	d0, dn := Orthogonality_parameters(LU, 300, rank, scaled_vol);


	FILE := Open(file_data, "a");
	for p in d do
	    fprintf FILE, "%o\t", p;
	end for;
	fprintf FILE, "%o\t%o\t%o\n", RR!scaled_vol, RR!d0, RR!dn;
	delete FILE;
	
    end for;
    
end if;
 
exit;
