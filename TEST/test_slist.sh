#!/bin/bash

A=./slist_dats

OUTPUT=$(cat <<END
input: specify input
output: specify output
help: print help
found input, the help text is: specify input
found help, the help text is: print help
sorry, the variable named anything is not found
END
)

if [[ $(eval '$A') != $OUTPUT ]]; then
    echo "1" && exit 1
fi
