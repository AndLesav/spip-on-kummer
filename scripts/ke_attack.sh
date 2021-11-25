#!/bin/bash

if (( $# < 7 )); then
    echo -e  "\033[31merror in $0:\033[0m need at least 4 argument";
    echo "....kf_units.h EXP_G PRIME REDUC EXP_E LENGTH_MAX PRIME_1...PRIME_s";
    echo "    ....EXP_G, EXP_E: field exponents (ground field and ext resp.)";
    echo "    ....PRIME_G: prime defining ground field";
    echo "    ....REDUC: reduction used : lll or bkz";
    echo "    ....LENGTH_MAX: max sequence length defining the extension";
    echo "    ....PRIME_i: first prime of a sequence defining the ext";
    exit;
fi


EXP_G=$1;
PRIME_G=$2;
RED_VERSION=$3
EXP_E=$4;
LENGTH_MAX=$5;


# Script folder
EXE_DIR=$(dirname $(readlink -f $0));
DATA_ROOT=$(dirname ${EXE_DIR});
DATA_ROOT="../";
DATA_DIR="${DATA_ROOT}/data_ke";
LOGS_DIR="${DATA_ROOT}/logs_ke";


# Just check that parent folders are indeed where they should be
[[ ! -d ${DATA_DIR} ]] && {
    echo -e "\x1b[31m[Err]\x1b[0m Data directory ${DATA_DIR} does not exist.";
    exit 1;
};

[[ ! -d ${LOGS_DIR} ]] && {
    echo -e "\x1b[31m[Err]\x1b[0m Logs directory ${LOGS_DIR} does not exist.";
    exit 1;
};

for ((i=2; i<=LENGTH_MAX; i++)); do
  
    echo "GROUND_EXP := ${EXP_G};" > "HEAD_FILE";
    echo "EXT_EXP := ${EXP_E};" >> "HEAD_FILE";
    echo "GROUND_PRIME := ${PRIME_G};" >> "HEAD_FILE";
    echo "RED_VERSION := \"${RED_VERSION}\";" >> "HEAD_FILE";
    echo "LENGTH_EXT := ${i};" >> "HEAD_FILE";

    primes="[$6";
    for ((j=7; j<=$#; j++)); do
	primes="${primes},${!j}";
    done;
    primes="${primes}]";

    echo "PRIMES := ${primes};" >> "HEAD_FILE";
    
    cat "HEAD_FILE" "ke_attack.m" > "ke_attack_${EXP_G}_${PRIME_G}__${EXP_E}_${i}_${RED_VERSION}.m";
done;

for ((i=2; i<=LENGTH_MAX; i++)); do
# for ((i=LENGTH_MAX; i<=LENGTH_MAX; i++)); do
    magma "ke_attack_${EXP_G}_${PRIME_G}__${EXP_E}_${i}_${RED_VERSION}.m" 1>"${LOGS_DIR}/ke.attack_${EXP_G}_${PRIME_G}__${EXP_E}_${i}_${RED_VERSION}" 2>&1 &
done;



exit 0;
