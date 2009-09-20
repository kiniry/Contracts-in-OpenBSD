#!/usr/bin/perl
	use strict; use warnings;
	my $path = shift;
	die unless $path;
	open (LIST, "$path/T1_HeaderName_FuncName.txt") or die $!;
	open (CALLS, "$path/T2_FuncCallee.txt")  or die $!;
	open (COUNTS, "> $path/T3_Count_Header_Func.txt")  or die $!;
	print scalar localtime();
	my @funcs = <LIST>;	
	close(LIST);			
	my @calls = <CALLS>;	
	close(CALLS);			

	my $func;
	foreach $func (@funcs)
	{
		 
	   $func =~ s/\n//g;
	   my ($header, $name) = split(/\s/, $func);
	   my @matches = grep(/^$name$/, @calls);
	   my $count = @matches;
	   print COUNTS "$count\t$func\n";
	}
	print "\n";
	print scalar localtime();
	close COUNTS;
	system("start notepad $path/T3_Count_Header_Func.txt");
   