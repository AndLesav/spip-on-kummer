EnoughCharacters := function(U, field_sequence, field_exponent) /* Calculate p-adic characters and put the result into a matrix */
    Q := [];
    field_length := #field_sequence;
    field_dim := field_exponent^field_length;
    r := #U;
    C := [1 : i in [1..field_length]];
    M := [];

    b_f, b_quo := KF_primefree_basis(field_sequence, field_exponent);

    q := 2;
    while (#Q lt Round(3*r)+Round(2*Sqrt(r))+field_dim) do
	/* "finding one prime"; */
	q := One_good_prime(field_sequence, C, q, field_exponent);
	F_q := GF(q);

	basis_q := KF_naive_basis_q_new(field_sequence, field_exponent, F_q);
	t := 0;
	E := [];
	for i in [1..r] do
	    /* "calculating embedding"; */
	    e := Embedding_q(U[i], field_sequence, field_exponent, F_q, basis_q: basis_vector := b_quo);
	    if (e eq 0) then
		break;
	    else
		t := t + 1;
		Append(~E, e);
	    end if;
	end for;
	
	if (t eq r) then	/* test if q is good for every element in U */
	    Q1 := Include(Q, q);
	    if Q1 ne Q then	/* test if the good q hasn't been chosen before */
		Q := Q1;
		zeta := RootOfUnity(field_exponent, F_q);
		Char_q := [ E[i]^((q-1) div field_exponent) : i in [1..r] ];
		Row_q := [ Log(zeta, (Char_q)[j]) : j in [1..r] ];
		Append(~M, Row_q);
	    end if;
	end if;   
    end while;
    return Matrix(GF(field_exponent), M);
end function;



/* calculate p-adic characters -- relative version */
Relative_EnoughCharacters := function(U, ground_field, extension)
    Q := [];
    ground_length := #ground_field[1];
    ext_length := #extension[1];
    ext_dim := extension[2]^ext_length;
    r := #U;
    C_ground := [1 : i in [1..ground_length]];
    C_ext := [1 : i in [1..ext_length]];
    M := [];
    q := 2;
    
    while (#Q lt Round(3*r)+Round(2*Sqrt(r))+ext_dim+ground_length^ground_field[2]) do
	q := Relative_one_good_prime(ground_field, extension, C_ground, C_ext, q);
	F_q := GF(q);
	basis_q := Relative_naive_basis_q(ground_field, extension, F_q);
	t := 0;
	E := [];
	for i in [1..r] do
	    e := Relative_embedding_q(U[i], ground_field, extension, F_q:basis:=basis_q);
	    if (e eq 0) then
		break;
	    else
		t := t + 1;
		Append(~E, e);
	    end if;
	end for;
	if (t eq r) then /* test if q is good for every element in U */
	    Q1 := Include(Q, q);
	    //Round(Log(2, q));
	    if Q1 ne Q then         /* test if the good q hasn't been chosen before */
		//F_q := GF(q);
		Q := Q1;
		if extension[2] eq 2 then
		    zeta := F_q!(-1);
		else
		    zeta := RootOfUnity(extension[2], F_q);
		end if;
		Char_q := [ E[i]^((q-1) div extension[2]) : i in [1..r] ];
		Row_q := [ Log(zeta, (Char_q)[j]) : j in [1..r] ];
		Append(~M, Row_q);
	    end if;
	end if;   
    end while;
    return Matrix(GF(extension[2]), M);
end function;
