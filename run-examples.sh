#!/bin/sh
che build lisp.c a.out

example () {
    n=`./a.out < examples/$1 | tail -n 1`
    if [ "$n" != $2 ]; then
        echo $1: wanted $2, got $n
        exit 1
    fi
}

example "1-1-7" "1.41421"
