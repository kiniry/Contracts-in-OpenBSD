#Arbitrary gotos
#only forward gotos, not jumping into nested blocks, are allowed. There is no plan to support arbitrary gotos in the future. 
#Function pointers
#Arbitrary cast
#•from integers to pointers, from pointer to integers: no support 
#•between pointers: experimental support, only for casts in code, not logic 
#Note: casts between integer types are supported 
#Union types
#experimental support, both in code and annotations 
#Variadic C functions
#unsupported 
#Floating point computations
#By default, float and double numbers are interpreted as reals. Consequently, it is not possible to check properties relaed to rounding errors or overflows. 
#Experimental supports for other models are described below, see description of the FloatModel pragma 

#!/usr/bin/perl
	use strict; use warnings;
	my $path = shift;
	die unless $path;
	open (FILTERED, "> $path/T7_State_Count_Header_Func_Source.txt") or die $!;
	open (DETAILED_COUNT, "$path/T6_Filtered_Count_Header_Func_Source.txt")  or die $!;
	my @funcs = <DETAILED_COUNT>;	
	close(DETAILED_COUNT);			
	print scalar localtime();

	my $func;
	foreach $func (@funcs)
	{
		$func =~ s/\n//g;
	  	my ($count, $header, $funcn, $file) = split(/\s/, $func);
	  	my $ret = checks($file);
 
	  	if ($ret == 0)
	  	{
	   		print FILTERED "-\t$func\n";
	  	}
	  	elsif ($ret == 1) 
	  	{	 
	   		print FILTERED "+\t$func\n"; 
	  	}
	  	elsif ($ret == 2)
	  	{
			print FILTERED "!\t$func\n";
	  	}
	  	else
	  	{
	  		print FILTERED "?\t$func\n";
	  	}
	}

	print "\n";
	print scalar localtime();
	
	close FILTERED;
	close DETAILED_COUNT;
	system("start notepad $path/T7_State_Count_Header_Func_Source.txt");
	
	sub checks
	{
		my $file = shift;
	  
	  	open (IMPL, $file) or return -1;
	  
	  	my @lines = <IMPL>;
	 
	 	my $ret = 1; 
	  	my $line;
	  	foreach $line (@lines)
	  	{
			$ret = 2 if (($line =~ /goto\s+\w+;/)  
			    || ($line =~ /\(\*\w+\)\(.*\)/)
			 	|| ($line =~ /\(\w+\s*\*\)\w+/)
			   );
			 
			$ret = 0 if (($line =~ /union/) || ($line =~ /\(.*,\s*\.\.\.\)/));
	  	}
	  	close IMPL;
	  	return $ret;
	}
	