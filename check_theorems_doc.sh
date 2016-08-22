#!/bin/bash
# checks whether a reference to a theorem in a Haskell file (with "-- Theorem: ") is mentioned in the Isabelle-checked documentation
# (provides no protection against just putting that theorem name into a comment or similar.)

THEOREMS_IN_HS=$(find ./haskell_tool -name '*.hs' | xargs grep -i '\-\-[[:space:]]*Theorem:[[:space:]]' | awk -F ': *' '{ print $3 }')

RED='\033[0;31m'
NC='\033[0m' # No Color

function check_thm {
	filename="./thy/Iptables_Semantics/Documentation.thy"
	if [ -n "$(grep "$@" $filename)" ]; then
	    echo -n " [ok]"
	 else
	    echo -ne " [${RED}FAIL${NC}]"
	    exit -1
	 fi
}

#echo "$THEOREMS_IN_HS"

#http://askubuntu.com/questions/344407/how-to-read-complete-line-in-for-loop-with-spaces
IFS=$'\n'
for THM in $THEOREMS_IN_HS; do
    echo -n "theorem $THM"
    check_thm $THM
    echo
done

exit 0
