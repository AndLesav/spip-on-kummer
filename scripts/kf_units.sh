#!/bin/bash

if (( $# < 4 )); then
    # echo -e "\x1b[31m[Err]\x1b[0m Data directory ${DATA_DIR} does not exist.";
    echo -e  "\033[31merror in $0:\033[0m need at least 4 argument";
    echo "....kf_units.h EXP LENGTH_MAX PRIME_1 ... PRIME_2";
    echo "    ....EXP: field exponent";
    echo "    ....LENGTH_MAX: max sequence length defining the field";
    echo "    ....RED_VERSION: reduction used : lll or bkz";
    echo "    ....PRIME_i: first prime of a sequence defining the field";
    exit;
fi


EXP=$1;
LENGTH_MAX=$2;
RED_VERSION=$3

# Script folder
EXE_DIR=$(dirname $(readlink -f $0));
DATA_ROOT=$(dirname ${EXE_DIR});
DATA_ROOT="../";
DATA_DIR="${DATA_ROOT}/data_kf";
LOGS_DIR="${DATA_ROOT}/logs_kf";


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
    
    echo "FIELD_EXP := ${EXP};" > "HEAD_FILE";
    echo "LENGTH := ${i};" >> "HEAD_FILE";
    echo "RED_VERSION := \"${RED_VERSION}\";" >> "HEAD_FILE";

    primes="[$4";
    for ((j=5; j<=$#; j++)); do
	primes="${primes},${!j}";
    done;
    primes="${primes}]";

    echo "PRIMES := ${primes};" >> "HEAD_FILE";
    
    cat "HEAD_FILE" "kf_units.m" > "kf_units_${EXP}_${i}_${RED_VERSION}.m";
done;

for ((i=2; i<=LENGTH_MAX; i++)); do
    magma "kf_units_${EXP}_${i}_${RED_VERSION}.m" 1>"${LOGS_DIR}/kf.units_${EXP}_${i}_${RED_VERSION}" 2>&1 &
done;



exit 0;
