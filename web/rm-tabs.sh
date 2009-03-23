#!/bin/bash

for i in examples/*.c; do
				echo "Replacing tabs from $i"
				sed "s/\t/  /" -i $i
				echo "Removing trailing whitespace"
				sed -e :a -e '/^\n*$/{$d;N;ba' -e '}' -i $i
done
