#!/usr/bin/env bash

check() {
    run sh -c "echo '$1' | python3 arith.py $1"
    echo "$1 = $2, your code outputs $output"
    [ "$output" = "$2" ]
}
