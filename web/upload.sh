#!/bin/bash

for i in `find * | grep -v "^\."`; do
				echo "Copying file: " $i
				scp $i tyr.diku.dk:/vol/www/hjemmesider/ansatte/jespera/
done

