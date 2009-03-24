#!/bin/bash

./insert-diffs.pl doc.html > tmp.html
mv tmp.html doc.html
rm -f tmp.html
