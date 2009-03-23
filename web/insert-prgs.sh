#!/bin/bash
#n=`echo $1 | sed "s/.html/.xhtml/"`
#echo "Copying $1 to $n"
#cp $1 $n
for i in examples/*.c; do
				b=`basename $i`
#				sed "s/FILE/$b/" -i insert.sed
				echo "Inserting program : " $b
				./insert-prgs.pl $1 $b > tmp.html
				mv tmp.html $1
				rm -f tmp.html
#				sed -f insert.sed -i $n
#				sed "s/$b/FILE/" -i insert.sed
done

