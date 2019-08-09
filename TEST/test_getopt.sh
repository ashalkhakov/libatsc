#!/bin/bash

A=./getopt_dats

if [[ $($A) ]]; then
    echo "1" && exit 1
fi
if [[ $($A -- | xargs) ]]; then
    echo "2" && exit 1
fi
if [[ $($A --help | xargs) != "long([help])" ]]; then
    echo "3" && exit 1
fi
if [[ $(eval '$A -- --help') != "positional(0, [--help])" ]]; then
    echo "4" && exit 1
fi
if [[ $(eval '$A --foobar --baz') != "long([foobar])long([baz])" ]]; then
    echo "5" && exit 1
fi
# foobar is flag
if [[ $(eval '$A --foobar=1 -b') != "long([foobar])positional(0, [1])positional(1, [-b])" ]]; then
    echo "6" && exit 1
fi
# -f requires an argument
if [[ $(eval '$A -xf foobar.txt') != "short([x])short([f], [foobar.txt])" ]]; then
    echo "7" && exit 1
fi
if [[ $(eval '$A --file 1 -b') != "long([file], [1])short([b])" ]]; then
    echo "8" && exit 1
fi
if [[ $(eval '$A --file=1 2') != "long([file], [1])positional(0, [2])" ]]; then
    echo "9" && exit 1
fi
if [[ $(eval '$A --output foo') != 'long([output], [foo])' ]]; then
    echo "10" && exit 1
fi
if [[ $(eval '$A -o foo') != 'short([o], [foo])' ]]; then
    echo "11" && exit 1
fi
if [[ $(eval '$A ./foo.dats -h') != 'positional(0, [./foo.dats])positional(1, [-h])' ]]; then
    echo "12" && exit 1
fi
if [[ $(eval '$A -xf foo.tar.gz') != 'short([x])short([f], [foo.tar.gz])' ]]; then
    echo "13" && exit 1
fi
if [[ $(eval '$A 1 2') != 'positional(0, [1])positional(1, [2])' ]]; then
    echo "14" && exit 1
fi
if [[ $(eval '$A --file -h') != 'please supply the required parameter for option --file' ]]; then
    echo "15" && exit 1
fi
if [[ $(eval '$A 1 2 3 4 5 6') != 'positional(0, [1])positional(1, [2])positional(2, [3,4,5,6])' ]]; then
    echo "16" && exit 1
fi
