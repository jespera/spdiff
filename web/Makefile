SHELL=/bin/bash

pages: insert *.html
	
upload:

insert: examples/*.c doc.html notabs
	./insert-prgs.sh doc.html

notabs: examples/*.c
	./rm-tabs.sh
