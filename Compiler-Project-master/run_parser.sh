#!/usr/bin/env bash

set -xe
if [ -d output ]; then
    rm -rf output
fi
mkdir output

cd src
for input in `ls ../tests/input2/`; do
    # echo $input
    rm -f parsetab.{py,pyc}
    rm -f parser.out
    python3 parser.py --output="../output/${input}.dot" "../tests/input2/${input}"
    dot -Tpdf "../output/${input}.dot" -o "../output/${input}.pdf"
    rm "../output/${input}.dot"
    rm -f parsetab.{py,pyc}
    rm -f parser.out
done
cd ..
