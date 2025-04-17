#!/bin/sh
che build lisp.c a.out

example () {
    n=`./a.out < examples/$1 | tail -n 1`
    if [ "$n" != $2 ]; then
        echo $1: wanted $2, got $n
        exit 1
    fi
}

example "1-1-7-sqrt" "1.41421"
example "1-1-7-curt" "2.1545"
example "1-1-8-scope" "1.73215"
example "1-1-8-scope-lexical" "1.73215"
