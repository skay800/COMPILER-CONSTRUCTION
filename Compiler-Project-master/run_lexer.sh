#!/usr/bin/env bash

if [ -d output ]; then
    rm -rf output
fi
mkdir output

cd src
for input in `ls ../tests/input2/`; do
    for config in `ls ../tests/cfg1/`; do
        python3 lexer.py --cfg="../tests/cfg1/${config}" --out="../output/${input}_${config}.html" "../tests/input2/${input}"
    done
done
cd ..
