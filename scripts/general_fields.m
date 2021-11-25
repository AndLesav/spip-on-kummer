load "../src/start_file.m";
SetClassGroupBounds("GRH");
p<x> := PolynomialRing(Integers());


P := [];

/* Q := PrimesInInterval(5, 500); */
Q := [2];


/* Q := []; */
E := 2;

s_file := "powers_of_";
/* s_file := "power_of_"; */
/* s_file := "primes"; */
/* s_file := ""; */
/* s_file := "consecutive"; */
/* s_file := "new_"; */

TYPE_LOG := "flat";
/* TYPE_LOG := ""; */

TYPE_L1 := "gaussian";
TYPE_L1 := "gamma";


for q in Q do
    /* k := E; */
    for k in [1..10] do
	if q^k gt 15 and q^k lt 1048 then
	    Append(~P, q^k);
	end if;
    end for;
end for;

/* P := Q; */
Sort(~P);
print P;
		
file_cyclo_basis := "../data_cyclo/data_cyclo_basis" cat "_" cat TYPE_LOG cat "_" cat s_file cat IntegerToString(E);
file_cyclo_key := "../data_cyclo/data_cyclo_key" cat "_" cat TYPE_LOG cat "_" cat s_file cat IntegerToString(E);


/* file_cyclo_basis := "../data_cyclo/data_cyclo_basis" cat "_" cat TYPE_LOG cat "_" cat s_file cat IntegerToString(E); */
/* file_cyclo_key := "../data_cyclo/data_cyclo_key" cat "_" cat TYPE_LOG cat "_" cat s_file cat IntegerToString(E); */



RR := RealField(4);

for q in P do

    print "********** Field with conductor ", q, " *********";
    
    /* Cyclotomic field */
    K := CyclotomicField(q);
    r1, r2 := Signature(K);
    CL := MyCyclotomic_units_log(q, K: prec:=500, type:=TYPE_LOG);

    RC := Sqrt(Determinant(Lattice(Matrix(CL))));
    
    /* scaled_vol := Root(RC, Rank(Matrix(CL))); */
    scaled_vol := Exp(Log(RC)/Rank(Matrix(CL)));
    
    c := Stats_log_norm_proj(K, 0, 500, RC: size_set:=500, p:=1/2, n:=10, shape:="uni", supp:=1, file:="", type_log := TYPE_LOG);
    /* print c; */
    
    r := #CL;
    /* M := IdentityMatrix(RationalField(), r); */
    N := [CL[i] : i in [1..r]];
    /* N := (2^5)*Matrix(N); */
    /* N := HorizontalJoin(M, N); */
    N := Matrix(N);
    N := RowSubmatrixRange(LLL(N: Delta:=0.99), 1, Rank(N));
    
    norms, enum, enum_key, hf := My_BKZ(N, RC, c);
    
    FILE := Open(file_cyclo_key, "a");
    fprintf FILE, "%o  %o %o  %o %o  %o  %o %o  %o  %o  %o  %o %o  %o %o %o  %o\n", EulerPhi(q), RR!scaled_vol, RR!c[1], RR!c[2], RR!c[3], RR!c[4], RR!c[5], RR!enum_key[1][1], RR!enum_key[1][2], RR!enum_key[1][3], RR!enum_key[1][4], RR!enum_key[1][5], RR!enum_key[2][1], RR!enum_key[2][2], RR!enum_key[2][3], RR!enum_key[2][4], RR!enum_key[2][5];
    delete FILE;

    FILE := Open(file_cyclo_basis, "a");
    fprintf FILE, "%o  %o  %o  %o  %o  %o  %o  %o  %o  %o \n", EulerPhi(q), RR!scaled_vol, RR!hf[1][1], RR!hf[1][2], RR!hf[2][1], RR!hf[2,2], RR!enum[1][1], RR!enum[1][2], RR!enum[2][1], RR!enum[2][2];
    delete FILE;
end for;
