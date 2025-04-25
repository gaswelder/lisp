#!/bin/sh
che build lisp.c a.out

example () {
    n=`./a.out < examples/$1 | tail -n 1`
    if [ "$n" != $2 ]; then
        echo $1: wanted $2, got $n
        exit 1
    fi
    echo "ok $1"
}

example "1-1-7-sqrt" "1.41421"
example "1-1-7-curt" "2.1545"
example "1-1-8-scope" "1.73215"
example "1-1-8-scope-lexical" "1.73215"
example "1-2-1-ackermann" "1024"
example "1-2-1-fac" "720"
example "1-2-1-fac-iter" "720"
example "1-2-1-fib" "144"
example "1-2-1-fib-iter" "832040"
example "1-2-2-count-change" "292"
example "count-tail" "1000"
example "count-tail-cond" "1000"
example "1-2-3-sine" "-0.4"
example "1-2-4-fast-expt" "2048"
example "1-2-5-gcd" "2"
example "1-2-6-prime" "true"
