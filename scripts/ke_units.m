/* computation of units */

load "../src/start_file.m";

Pol_ring<x> := PolynomialRing(Integers());
SetClassGroupBounds("GRH");

RR := RealField(5);



ground := <[GROUND_PRIME], GROUND_EXP>;

/* RED_VERSION := "lll"; */
/* RED_VERSION := "bkz"; */

GRH_BOOL := true;

for q in PRIMES do

    /* ASSUMES GROUND_PRIME is not in PRIMES */

    /* d := [q]; */
    ext := <[q], EXT_EXP>;
    ext_length := LENGTH_EXT;
    q1 := q;
    
    while #ext[1] lt ext_length do
	q1 := NextPrime(q1);
	if (q1 ne GROUND_PRIME) then
	    Append(~ext[1], q1);
	end if;
    end while;
    
    /* ext := <d, EXT_EXP>; */


    /* defining files name */
    file_end := "_" cat IntegerToString(ground[2]) cat "_" cat IntegerToString(ext[2]) cat "_" cat (&cat ["_" cat IntegerToString(ground[1,i]) : i in [1..#ground[1]]]) cat "_" cat (&cat ["_" cat IntegerToString(ext[1,i]) : i in [1..#ext[1]]]) ;
    file_units := "../data_ke/UNITS/units" cat file_end;
    file_data := "../data_ke/units_" cat IntegerToString(ground[2]) cat "_" cat IntegerToString(ground[1][1]) cat "_" cat IntegerToString(ext_length) cat "_" cat RED_VERSION;

    
    /* /\* defining files names *\/ */
    /* file_end := (&cat ["_" cat IntegerToString(d[i]) : i in [1..#d]]) cat "__" cat IntegerToString(FIELD_EXP) cat "_" cat RED_VERSION; */
    /* file_units := "../data_kf/UNITS/units" cat file_end; */
    /* file_data := "../data_kf/units_" cat IntegerToString(FIELD_EXP) cat "_" cat IntegerToString(LENGTH) cat "_" cat RED_VERSION; */
    
    precision_log := 8000;
    
    print "PRECISION LOG IS: ", precision_log;
    
    t := Cputime();
    U, list, prec, lattice, uni := Relative_units_real(ground, ext, precision_log: grh:=GRH_BOOL, red_version:=RED_VERSION);

    TIME_UNITS := Cputime(t);

    print "UNITS COMPUTED";
    
    lattice1 := [Eltseq(lattice[i]) : i in [1..Nrows(lattice)]];
    uni1 := [Eltseq(uni[i]) : i in [1..Nrows(uni)]];
    
    FILE := Open(file_units, "w");
    fprintf FILE, "[* %o, %o, %o, Matrix(%o), Matrix(%o), %o *]", U, list, prec, lattice1, uni1, precision_log;
    delete FILE;

    LU := Matrix([U[i,2] : i in [1..#U]]);

    LU := RowSubmatrixRange(LLL(LU: Delta:=0.99), 1, Rank(LU));
    RU := RealField(15)! ( Sqrt(Determinant(ChangeRing(LU*Transpose(LU), RealField(500)))));

    r1, r2 := Relative_extension_signature(ground, ext);
    rank := r1+r2-1;
    
    scaled_vol := Exp(Log(RU)/rank);
    
    FILE := Open(file_data, "a");
    fprintf FILE, "%o ", ext[2];
    for p in ext[1] do
	fprintf FILE, "%o ", p;
    end for;
    
    fprintf FILE, "%o %o\n", RR!scaled_vol, RR!TIME_UNITS;
    delete FILE;
    
    delete U, list, uni, lattice;

end for;

exit;
