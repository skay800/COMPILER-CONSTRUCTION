#!/usr/bin/env bash

set -xe
if [ -d output ]; then
    rm -rf output
fi
mkdir output
mkdir output/irs
mkdir output/sts

cd src
for input in `ls ../tests/input2/`; do
    echo $input
    python3 semantic_parser.py --ir="../output/irs/${input}.ir" --st="../output/sts/${input}.st" "../tests/input2/${input}"
done
cd ..
