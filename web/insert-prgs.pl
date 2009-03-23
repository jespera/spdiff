#!/usr/bin/perl

$html_name = $ARGV[0];
$c_tag = $ARGV[1];

open(cfile, "examples/" . $c_tag);
@clines = <cfile>;

open(hfile, $html_name);

while ($line = <hfile>) {
				if ($line =~ /<!-- (.*) -->/ && $c_tag eq $1)
				{
								print $line;
								$line = <hfile>;
								if ($line =~ /<pre>/) {
									print $line;
									$flag = 1;
									while ($flag == 1) {
													$line = <hfile>;
													if ($line =~ /<\/pre>/) {
																	$flag = 0;
																	print @clines;
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

close(cfile);
close(hfile);
