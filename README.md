# SPIP over Kummer extensions

Code in support of the article "On the Shortest Principal Ideal Problem over Kummer 
extensions".

## Authors
Andrea Lesavourey, Thomas Plantard, Willy Susilo.

## Softwares
The code has been tested with Magma V2.24-9.


## Warning
This code does not come with any guarantee. 


### ACKNOWLEDGMENTS
We *deeply* thank Olivier Bernard from who we got the inspiration for the organisation of the scripts. 


## How to use scripts?

For a Kummer extension of the form L = K (sqrt[p]{m1}, ... sqrt[p]{mr}) with
K = QQ(sqrt[q]{n1}, ..., sqrt[q]{ms}), our scripts allows to compute the unit group,
simulate attacks as described in the paper, and evaluate the quality of the bases
obtained in the cases where:
- mi and nj are prime integers
- for all i,j we have mi =/= nj
- s = 1, i.e. K is a simple field

In the following <reduc> will designate the lattice reduction method chosen : LLL or
BKZ_20.

From the root directory, go in the directory "./scripts/" then, 
to produce data as in the article, one should do as follows.

1. Compute desired units with:
   - bash kf_units.sh *<p> <r_max> <reduc> <m1> ... <mt>* for Kummer fields with one
   exp
   - bash kf_units.sh <q> <n> <reduc> <p> <r_max> <m1> ... <ms> for Kummer fields with two
   exp

   <r_max> is the max length for which the units will be computed (starting from r=2),
   and each <mi> is the starting prime integer of a field defining sequence: for
   example if one uses the command
                      *bash kf_units.sh 3 3 lll 2 3 5*
   then two processes will be launched in parallel: one computing the units of
   fields of the form QQ(sqrt[3]{p1}, sqrt[3]{p2}) and the other fields of the form
   QQ(sqrt[3]{p1}, sqrt[3]{p2}, sqrt[3]{p3}) , where p1 = m1, m2 and m3 successively.
   Initially, one has p{i+1} = NextPrime(pi).
   
   The logs will be printed in: ../logs_kf(e)/ under the names kf.units_exp_r_reduc
   and ke.units_q_n__p_r_reduc (for r <= r_max) ;
   the units are printed in ../data_kf(e)/UNITS/  and the files for units are
   units_p_r_reduc and units_q_n_r_lll resp.
   
   
Then if 1. has been completed, one can:

2. Launch attacks with:
   - bash kf_attack.sh <p> <r> <reduc> <m1> ... <mt> for Kummer fields with one
   exp
   - bash ke_attack.sh <p> <r> <reduc> <m1> ... <mt> for Kummer fields with one
   exp

   Print files follow the same rules as explained for units.


Only for Kummer extensions with one exponent:

3. Compute some orthogonality parameters with:
   - bash kf_eval_geo.sh <p> <r> <reduc> <m1> ... <mt> for Kummer fields with one
   exp

   Print files for data are of the form  ortho_param_*


4. Compute the enumeration costs with:
   - *bash kf_enum_cost.sh p r  m1 ... mt* for Kummer fields with one
   exp

   Both type of reductions are treated. Print files for data are of the form
   key_enum_* , basis_enum_* and key_stats_*


5. Compute enumeration costs and orthogonality parameters for cyclotomic fields with:
   - magma general_fields.m > log_file_of_your_choice 

   One need to modify this file to choose from prime or powers-of-2 conductors.
   Print files for data are in ../data_cyclo/



The scripts print "temporary" files in the "scripts" directory that can been cleaned up
by :  bash ./clean.sh


### Summary of the directories from root
 "./src": Most functions
 "./scripts": Bash/magma scripts + magma functions for experiments in data_and_tests.m
 "./data_kf": data for Kummer fields with one exponent
 "./data_ke": data for Kummer fields with two exponents
 "./logs_kf": logs for Kummer fields with one exponent
 "./logs_ke": logs for Kummer fields with two exponents
 

## License
&copy; 2021, Andrea Lesavourey, Thomas Plantard, Willy Susilo.  
This work is published under the GNU General Public License (GPL) v3.0.  
See the LICENSE file for complete statement.
