#!/bin/bash

A=./argp_dats

HELP='Usage: argp [--parents] [--help] [--version] DEST SOURCE
Options:
  -p|--parents    no error if existing, make directories as needed
  -h|--help       display this help and exit
  -v|--version    output version information and exit
'
SD='
source file: foo
destination file: -
'

if [[ $(eval '$A --help') != $HELP ]]; then
    echo "0" && exit 1
fi
if [[ $(eval '$A -h') = $(eval '$A --help') ]]; then
    echo "1" && exit 1
fi
if [[ $(eval '$A -v') = "argp 0.0.1
" ]]; then
    echo "2" && exit 1
fi
if [[ $(eval '$A') = $(eval '$A --help') ]]; then
    echo "3" && exit 1
fi
if [[ $(eval '$A foo -') = $SD ]]; then
    echo "4" && exit 1
fi
