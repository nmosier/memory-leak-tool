#!/usr/local/bin/bash

for ARG in "$@"; do
    make "$ARG"
    time ../src/main.py -b 100000 "$ARG"
done
