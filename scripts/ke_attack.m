/* computation of units */

load "../src/start_file.m";

Pol_ring<x> := PolynomialRing(Integers());
SetClassGroupBounds("GRH");

RR := RealField(5);


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


depth:=1;


ground := <[GROUND_PRIME], GROUND_EXP>;


GRH_BOOL := true;

for q in PRIMES do

    /* ASSUMES GROUND_PRIME is not in PRIMES */
    
    ext := <[q], EXT_EXP>;
    ext_length := LENGTH_EXT;
    q1 := q;
    
    while #ext[1] lt ext_length do
	q1 := NextPrime(q1);
	if (q1 ne GROUND_PRIME) then
	    Append(~ext[1], q1);
	end if;
    end while;
    
    /* defining files name */
    file_end := "_" cat IntegerToString(ground[2]) cat "_" cat IntegerToString(ext[2]) cat "_" cat (&cat ["_" cat IntegerToString(ground[1,i]) : i in [1..#ground[1]]]) cat "_" cat (&cat ["_" cat IntegerToString(ext[1,i]) : i in [1..#ext[1]]]) ;
    file_units := "../data_ke/UNITS/units" cat file_end;
    file_data := "../data_ke/attack_" cat IntegerToString(ground[2]) cat "_" cat IntegerToString(ground[1][1]) cat "_" cat IntegerToString(ext_length) cat "_" cat RED_VERSION;

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

    /* compute some parameters */
    LU := Matrix([U[i,2] : i in [1..#U]]);
    LU := RowSubmatrixRange(LLL(LU: Delta:=0.99), 1, Rank(LU));
    RU := RealField(15)! ( Sqrt(Determinant(ChangeRing(LU*Transpose(LU), RealField(500)))));
    r1, r2 := Relative_extension_signature(ground, ext);
    rank := r1+r2-1;
    scaled_vol := Exp(Log(RU)/rank);
    delete LU;

    
    n, ec, af := Relative_attack(ground, ext, NUMBER_KEYS, SIZE_KEYS, U, precision_log, NORMS_BOOL: p:=binom_p, n:=binom_n, shape:=KEY_SHAPE, supp:=1, list:=list, lattice:=lattice, uni:=uni, precision:=precision, decoding_method:=DECODING_METHOD, depth:=depth, enum_cost := false);

    
    FILE := Open(file_data, "a");
    fprintf FILE, "%o ", ext[2];
    
    for p in ext[1] do
	fprintf FILE, "%o ", p;
    end for;

    if #af eq 0 then
	fprintf FILE, "%o %o %o\n", RR!scaled_vol, RR!n[1]/NUMBER_KEYS, RR!n[2]/NUMBER_KEYS;
    else 
	fprintf FILE, "%o %o %o %o %o %o %o %o\n", RR!scaled_vol, RR!n[1]/NUMBER_KEYS, RR!n[2]/NUMBER_KEYS, RR!af[1], RR!af[2], RR!af[3], RR!af[4], RR!af[5];
    end if;
    delete FILE;
    
    delete U, list, uni, lattice;

end for;

exit;
