power_condition := function(prime_candidate, m, c, prime_exponent)
if (prime_candidate mod prime_exponent) eq 1 then
    exp := (prime_candidate-1) div prime_exponent;
    t := Modexp(m, exp, prime_candidate) ;
    if (((t eq 1) and (c eq 1)) or ((t ne 1) and (c eq 0))) then
	return true;
    else
	return false;
    end if;
else
    t := IsPower(GF(prime_candidate)!m, prime_exponent) ;
    if (((t eq true) and (c eq 1)) or ((t eq false) and (c eq 0))) then
	return true;
    else
	return false;
    end if;
end if;
end function;


One_good_prime := function(integers_seq, conditions_seq, prime_start, prime_exponent)
length := #integers_seq;
bool := false;
prime_candidate := prime_start;
while (bool eq false)  do
    prime_candidate := NextPrime(prime_candidate);
    while (prime_candidate mod prime_exponent) ne 1 do
	prime_candidate := NextPrime(prime_candidate);
    end while;
    test := true;
    count := 1;
    while (test and (count lt length+1)) do
	test and:= power_condition(prime_candidate, integers_seq[count], conditions_seq[count], prime_exponent);
	count +:= 1;
    end while;
    bool := test;
end while;
return prime_candidate;
end function;


Relative_one_good_prime := function(ground_field, extension, condition_ground, condition_ext, prime_start)
length_ground := #ground_field[1];
length_ext := #extension[1];
bool := false;
prime_candidate := prime_start;
while (bool eq false) do
    prime_candidate := NextPrime(prime_candidate);
    cond_ground := (prime_candidate mod ground_field[2]) eq 0;
    /* cond_ground or:= Order(GF(ground_field[2])!prime_candidate) ne (ground_field[2]-1); */
    //print cond_ground;
    while (cond_ground or ((prime_candidate mod extension[2]) ne 1)) do
	prime_candidate := NextPrime(prime_candidate);
	cond_ground := (prime_candidate mod ground_field[2]) eq 0;
	cond_ground or:= Order(GF(ground_field[2])!prime_candidate) ne (ground_field[2]-1);
    end while;
    test := true;
    count := 1;
    while (test and (count lt length_ground+1)) do
	test and:= power_condition(prime_candidate, ground_field[1][count], condition_ground[count], ground_field[2]);
	count +:= 1;
    end while;
    count := 1;
    while (test and (count lt length_ext+1)) do
	test and:= power_condition(prime_candidate, extension[1][count], condition_ext[count], extension[2]);
	count +:= 1;
    end while;
    bool := test;
end while;
return prime_candidate;
end function;
