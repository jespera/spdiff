#!/bin/bash

for i in `find * | grep -v "^\."`; do
				echo "Copying file: " $i
				#echo $(basename $i)
				#echo $(dirname $i)
				scp $i tyr.diku.dk:/vol/www/hjemmesider/ansatte/jespera/$(dirname $i)/
done

