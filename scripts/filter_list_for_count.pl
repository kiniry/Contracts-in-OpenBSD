#!/usr/bin/perl
    use strict; use warnings;
	my $detailed_txt_path = shift;
	my $thold = shift;
	die unless $detailed_txt_path;
	die unless $thold;
	open (FILTERED, '> count_filtered.txt') or die $!;
	open (DETAILED_COUNT, "$detailed_txt_path/detailed.txt")  or die $!;
	my @funcs = <DETAILED_COUNT>;	
	close(DETAILED_COUNT);			
	print scalar localtime();

	my $func;
	foreach $func (@funcs)
	{
	  $func =~ s/\n//g;
	  my ($count, $header, $funcn, $file) = split(/\s/, $func);
	  print FILTERED "$func\n" if ($count >= $thold);
	}

	print "\n";
	print scalar localtime();
	
	close FILTERED;
	system("start notepad count_filtered.txt");