/* computation of units */

load "../src/start_file.m";

Pol_ring<x> := PolynomialRing(Integers());
SetClassGroupBounds("GRH");

RR := RealField(5);


/* RED_VERSION := "lll"; */
/* RED_VERSION := "bkz"; */

GRH_BOOL := true;

field_dim := FIELD_EXP^LENGTH;

if field_dim lt 400 then

    for q in PRIMES do
	
	d := [q];
	while #d lt LENGTH do
	    Append(~d, NextPrime(d[#d]));
	end while;
	
	/* while #d lt LENGTH do */
	/*     q := Random(P); */
	/*     if (&and [(d[i] mod q) ne 0 : i in [1..#d]]) then */
	/* 	Include(~d, q); */
	/*     end if; */
	/* end while; */

	kf := <d, FIELD_EXP>;
	
	/* defining files names */
	file_end := (&cat ["_" cat IntegerToString(d[i]) : i in [1..#d]]) cat "__" cat IntegerToString(FIELD_EXP) cat "_" cat RED_VERSION;
	file_units := "../data_kf/UNITS/units" cat file_end;
	file_data := "../data_kf/units_" cat IntegerToString(FIELD_EXP) cat "_" cat IntegerToString(LENGTH) cat "_" cat RED_VERSION;
	
	/* computing simple units SU(K) to determine working log precision */
	U_simple, list, Reg := KF_simple_units(d, FIELD_EXP, 8000);
        V := [Log(2, Norm(Vector(U_simple[i,2]))) :  i in [1..#U_simple]];
	print &+V/field_dim;
	precision_log := LENGTH*(Ceiling(&+V / field_dim)) + field_dim*10;
	delete V, U_simple, list, Reg;

	print "PRECISION LOG IS: ", precision_log;
	
	t := Cputime();
	
        U, list, precision, lattice, uni := KF_units_real(d, FIELD_EXP, precision_log, true: red_version := RED_VERSION);
	
	/* print "precision after units computation is: ", precision; */

	TIME_UNITS := Cputime(t);

	print "UNITS COMPUTED";
	
	lattice1 := [Eltseq(lattice[i]) : i in [1..Nrows(lattice)]];
	uni1 := [Eltseq(uni[i]) : i in [1..Nrows(uni)]];
	
	FILE := Open(file_units, "w");
	fprintf FILE, "[* %o, %o, %o, Matrix(%o), Matrix(%o), %o *]", U, list, precision, lattice1, uni1, precision_log;
	delete FILE;

	LU := Matrix([U[i,2] : i in [1..#U]]);

	LU := RowSubmatrixRange(LLL(LU: Delta:=0.99), 1, Rank(LU));
	RU := RealField(15)! ( Sqrt(Determinant(ChangeRing(LU*Transpose(LU), RealField(500)))));

	r1, r2 := KF_signature(<d, FIELD_EXP>);
	rank := r1+r2-1;
        
	scaled_vol := Exp(Log(RU)/rank);
	
	FILE := Open(file_data, "a");
	for p in d do
	    fprintf FILE, "%o\t", p;
	end for;
	
	fprintf FILE, "%o\t%o\n", RR!scaled_vol, RR!TIME_UNITS;
	delete FILE;
	
	delete U, list, uni, lattice;

    end for;
end if;

exit;
