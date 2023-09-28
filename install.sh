#*******************************************************************************
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.
#   
# Copyright (c) 2021-2023 ETH Zurich.
#*******************************************************************************
#!/bin/bash

ROOT=~/SMT
PATH_SMTSolvers=$ROOT/SMTSolvers
PATH_UNSATY="$( cd "$( dirname "${BASH_SOURCE[0]}" )" > /dev/null 2>&1 && pwd )"

mkdir -p $ROOT
cd $ROOT

# download and build the Z3 version used in our experiments in the folder SMTSolvers
mkdir -p $PATH_SMTSolvers
cd $PATH_SMTSolvers

# Z3
wget https://github.com/Z3Prover/z3/archive/z3-4.12.1.tar.gz
tar -zxvf z3-4.12.1.tar.gz
rm z3-4.12.1.tar.gz
mv z3-z3-4.12.1 z3_4.12.1
cd z3_4.12.1
python scripts/mk_make.py --java
cd build
make

# clone smt-triggen and install PySMT
cd $ROOT
git clone https://github.com/alebugariu/smt-triggen Triggen 
curl -L https://github.com/alebugariu/pysmt/archive/refs/tags/v0.8.0-ale.tar.gz | tar xvz -C .
mv pysmt-0.8.0-ale pysmt

# compile our tool:
cd $PATH_UNSATY
mkdir -p classes
javac -d classes -cp "jars/commons-io-2.11.0.jar:jars/commons-cli-1.4.jar:$PATH_SMTSolvers/z3_4.12.1/build/com.microsoft.z3.jar" -sourcepath src src/evaluation/Main.java
chmod +x run.sh

export LD_LIBRARY_PATH=$PATH_SMTSolvers/z3_4.12.1/build
