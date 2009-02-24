#!/bin/bash

l=`grep "^\w.\+ \(\w\|_\)\+(.*)" -x $1 | sort | wc -l`
m=`grep "^\w.\+ \(\w\|_\)\+(.*)" -x $1 | sort -u | wc -l`

if [ $l = $m ]; then
				echo ""
else
				echo $1 has DUPLICATES
fi
