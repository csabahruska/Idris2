set -x -e
#export IDRIS2_PREFIX="../../install"
rlwrap ../../build/exec/idris2 --cg staging $@
