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

# Z3 [4.12.2 for UnsatY]
wget https://github.com/Z3Prover/z3/archive/z3-4.12.2.tar.gz
tar -zxvf z3-4.12.2.tar.gz
rm z3-4.12.2.tar.gz
mv z3-z3-4.12.2 z3-4.12.2
cd z3-4.12.2
python scripts/mk_make.py --java USE_OPENMP=1
cd build
make

# Z3 [4.8.10 for smt-triggen]
curl -L -O https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip
unzip z3-4.8.10-x64-ubuntu-18.04.zip
rm z3-4.8.10-x64-ubuntu-18.04.zip
mv z3-4.8.10-x64-ubuntu-18.04 z3-4.8.10

# clone smt-triggen and install PySMT
cd $ROOT
git clone https://github.com/alebugariu/smt-triggen Triggen
pip3 install -e Triggen 
curl -L https://github.com/alebugariu/pysmt/archive/refs/tags/v0.8.0-ale.tar.gz | tar xvz -C .
mv pysmt-0.8.0-ale pysmt

export PYTHONPATH=$ROOT/pysmt

# compile our tool:
cd $PATH_UNSATY
mkdir -p classes
javac -d classes -cp "jars/commons-io-2.11.0.jar:jars/commons-cli-1.4.jar:$PATH_SMTSolvers/z3-4.12.2/build/com.microsoft.z3.jar" -sourcepath src src/evaluation/Main.java
chmod +x run.sh

export PATH=$PATH:$PATH_SMTSolvers/z3-4.8.10/bin
