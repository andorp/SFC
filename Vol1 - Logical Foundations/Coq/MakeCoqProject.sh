#!/bin/sh

coq_makefile -f _CoqProject *.v -o Makefile
make
