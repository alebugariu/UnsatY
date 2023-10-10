#*******************************************************************************
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.
#   
# Copyright (c) 2021-2023 ETH Zurich.
#*******************************************************************************
#!/bin/bash

eval `cat install.sh | grep "^ROOT="`

PATH_SMTSolvers=$ROOT/SMTSolvers
PATH_UNSATY="$( cd "$( dirname "${BASH_SOURCE[0]}" )" > /dev/null 2>&1 && pwd )"
  
# run our tool:
export LD_LIBRARY_PATH=$PATH_SMTSolvers/z3-4.12.2/build

cd "$PATH_UNSATY"
java -Djava.library.path=$PATH_SMTSolvers/z3-4.12.2/build -cp "classes:jars/commons-io-2.11.0.jar:jars/commons-cli-1.4.jar:$PATH_SMTSolvers/z3-4.12.2/build/com.microsoft.z3.jar" evaluation.Main $*
