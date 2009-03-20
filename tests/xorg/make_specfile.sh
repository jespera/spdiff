rm -f specfile
for i in `find -type f -name "*.c"`; do
				echo "$i  $i" >> specfile
done
