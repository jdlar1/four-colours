#!/bin/sh
set -eu
gcc -std=gnu89 -O3 -march=native -w steinberger/discharge.c -o discharge
sed -e 's/weight\[8\]/weight[9]/g' -e 's/choice\[8\]/choice[9]/g' -e 's/interval\[10\]/interval[18]/g' -e 's/428506L, 1485003L};/428506L, 1485003L, 5178161L, 18155816L};/' steinberger/reduce.c > reduce16.c
gcc -O3 -march=native -std=gnu89 -w reduce16.c -o reduce
