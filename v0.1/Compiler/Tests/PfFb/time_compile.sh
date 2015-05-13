#!/bin/bash

echo Timing compilation of cpp files in $1
echo "file,time,cputime" > $1/compile-times.csv

for f in $1/sol*.cpp; do 
  echo "Processing $f file.."; 
  t=`/usr/bin/time -f "%e,%U" mpic++ $f -o timedexec 2>&1 | tail -n 1`
  echo $f,$t >> $1/compile-times.csv
  echo $t
done
