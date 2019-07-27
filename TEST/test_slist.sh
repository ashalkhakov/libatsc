#!/bin/bash

A=./slist_dats

OUTPUT=$(cat <<END
input: specify input
output: specify output
help: print help
END
)

if [[ $(eval '$A') != $OUTPUT ]]; then
    echo "1" && exit 1
fi
