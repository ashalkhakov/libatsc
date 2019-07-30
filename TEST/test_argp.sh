#!/bin/bash

A=./argp_dats

HELP=$(cat <<END
Usage: argp [--parents] [--help] [--version] DEST SOURCE
Options:
  -p|--parents    no error if existing, make directories as needed
  -h|--help       display this help and exit
  -v|--version    output version information and exit
END
)

# FIXME:
# argp --parents foo bar
# should be OK to call (parents doesn't take any params! so we MUST disambiguate it somehow)

if [[ $($A --help) != $HELP ]]; then
    echo "0" && exit 1
fi
if [[ $($A -h) != $($A --help) ]]; then
    echo "1" && exit 1
fi
if [[ $($A -v) != "argp 0.0.1" ]]; then
    echo "2" && exit 1
fi
if [[ $($A) != $($A --help) ]]; then
    echo "3" && exit 1
fi

# FIXME: argp -hv != argp -vh
# argp foo bar -- OK
