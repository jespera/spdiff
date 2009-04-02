#!/usr/bin/perl

$html_name = $ARGV[0];

open(hfile, $html_name);

while ($line = <hfile>) {
				# are we on a diff line ?
				if ($line =~ /<!-- exec: (.*) -->/) {
					$cmd = $1;
					print $line;
					$line = <hfile>;
					if ($line =~ /<pre.*>/) {
									print $line;
									$flag = 1;
									while ($flag == 1) {
													$line = <hfile>;
													if ($line =~ /<\/pre>/) {
																	$flag = 0;
																	system($cmd);
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
