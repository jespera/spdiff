#!/usr/bin/perl

$html_name = $ARGV[0];


open(hfile, $html_name);

while ($line = <hfile>) {
				# are we on a diff line ?
				if ($line =~ /<!-- diff (.*) (.*) -->/) {
					$old = $1;
					$new = $2;
					print $line;
					$line = <hfile>;
					if ($line =~ /<pre>/) {
									print $line;
									$flag = 1;
									while ($flag == 1) {
													$line = <hfile>;
													if ($line =~ /<\/pre>/) {
																	$flag = 0;
																	system("diff -u -t examples/$old examples/$new | tail --lines=+4");
																	print $line;
													}
									}
					} else {
									print $line;
					}
				} else {
							 print $line;
			  }	 
}
