#!/bin/bash

./insert-cmd.pl doc.html > tmp.html
mv tmp.html doc.html
rm -f tmp.html
