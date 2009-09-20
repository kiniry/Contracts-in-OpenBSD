#!/usr/bin/perl
	use strict; use warnings;
	my $path = shift;
	die unless $path;
	open (LIST, "$path/T4_Filtered_Count_Header_Func.txt") or die $!;
	open (IMPLS, "$path/T5_Func_Source.txt")  or die $!;
	open (FUNC_IMPLS, "> $path/T6_Filtered_Count_Header_Func_Source.txt")  or die $!;
	print scalar localtime();
	my @funcs = <LIST>;	
	close(LIST);			
	my @impls = <IMPLS>;	
	close(IMPLS);			

	my $func;
	foreach $func (@funcs)
	{
		$func =~ s/\n//g;
	   	my ($count, $header, $name) = split(/\s/, $func);
	   	my @matches = grep(/^$name\s+.+/, @impls);
	   
	   	my $match;
	   	foreach $match (@matches)
	   	{
	   		print FUNC_IMPLS "$func\t";
	   		if ($match =~ /$name\s+(.+)/)
	   		{
	   			print FUNC_IMPLS "$1";
	   		}
	   		else
	   		{
	   			print FUNC_IMPLS "?";
	   		}
	   		print FUNC_IMPLS "\n";
	   	}
	}
	print "\n";
	print scalar localtime();
	close FUNC_IMPLS;
	system("start notepad $path/T6_Filtered_Count_Header_Func_Source.txt");
   