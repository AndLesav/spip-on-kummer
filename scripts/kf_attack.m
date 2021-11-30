load "../src/start_file.m";

Pol_ring<x> := PolynomialRing(Integers());
SetClassGroupBounds("GRH");

RR := RealField(5);


/* RED_VERSION := "lll"; */
/* RED_VERSION := "bkz"; */


NUMBER_KEYS := 100;
KEY_SHAPE := "uni";
/* KEY_SHAPE := "binom"; */
binom_p := 1/2;
binom_n := 100;
SIZE_KEYS := 0;
SIZE_SUPPORT := 1;

NORMS_BOOL := true;
GRH_BOOL := true;

/* DECODING_METHOD := "cvp"; */
DECODING_METHOD := "babai";

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
	file_data := "../data_kf/attack_" cat IntegerToString(FIELD_EXP) cat "_" cat IntegerToString(LENGTH) cat "_" cat RED_VERSION;
	

	/* reading file where units are kept */
	s := Read(file_units);
	L := eval s;
	
	U := L[1];
	list := L[2];
	precision := L[3];
	lattice := L[4];
	uni := L[5];
	precision_log := L[6];

	delete L;
	

	LU := Matrix([U[i, 2] : i in [1..#U]]);
	LU := RowSubmatrixRange(LLL(LU: Delta:=0.99), 1, Rank(LU));
	RU := RealField(15)! ( Sqrt(Determinant(ChangeRing(LU*Transpose(LU), RealField(300)))));
	
	/* RU := MyRegulator(ChangeRing(MU, RealField(400))); */
	r1, r2 := KF_signature(<d, FIELD_EXP>);
	rank := r1+r2-1;
	scaled_vol := Exp(Log(RU)/rank);
        
	delete LU;
	
	NUMBER_SUCCESS := 0;
	NUMBER_SHORTER := 0;
	
	TIME_NORM := 0;
	TIME_DECODING := 0;
	TIME_ALG_RECONS := 0;
	TIME_ATTACK := 0;
	TIME_UNITS := 0;
		

	K := <d, FIELD_EXP>;

        n, ec, af, precision, lattice, uni := KF_attack(K, NUMBER_KEYS, SIZE_KEYS, U, precision_log, NORMS_BOOL: p:=binom_p, n:=binom_n, shape:=KEY_SHAPE, supp:=1, list:=list, lattice:=lattice, uni:=uni, precision:=precision, decoding_method:=DECODING_METHOD, enum_cost:=false, red_version:=RED_VERSION);


	FILE := Open(file_data, "a");
	if #af eq 0 then
	    fprintf FILE, "%o %o %o \t %o\n", FIELD_EXP, q, RR!scaled_vol, RR!n[1]/NUMBER_KEYS, RR!n[2]/NUMBER_KEYS;

	else 
	    fprintf FILE, "%o %o %o \t %o \t %o \t %o \t %o \t %o \t %o \t %o \n", FIELD_EXP, q, RR!scaled_vol, RR!n[1]/NUMBER_KEYS, RR!n[2]/NUMBER_KEYS, RR!af[1], RR!af[2], RR!af[3], RR!af[4], RR!af[5];
	end if;
	delete FILE;

        
	delete U, list, uni, lattice;
    end for;
end if;
exit;
