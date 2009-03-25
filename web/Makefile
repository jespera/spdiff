SHELL=/bin/bash

pages: insert *.html
	
upload: insert *.html
	./upload.sh

insert: examples/*.c doc.html notabs
	./insert-prgs.sh doc.html
	./insert-diffs.sh
	./insert-cmd.sh

notabs: examples/*.c
	./rm-tabs.sh
