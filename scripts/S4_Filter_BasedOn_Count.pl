#!/usr/bin/perl
    use strict; use warnings;
	my $path = shift;
	my $thold = shift;
	die unless $path;
	die unless $thold;
	open (FILTERED, "> $path/T4_Filtered_Count_Header_Func.txt") or die $!;
	open (DETAILED_COUNT, "$path/T3_Count_Header_Func.txt")  or die $!;
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
	system("start notepad $path/T4_Filtered_Count_Header_Func.txt");