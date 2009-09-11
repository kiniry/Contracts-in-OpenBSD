#!/usr/bin/perl
    use strict; use warnings;
	my $path = shift;
	die unless $path;
	open (IMPLS, '> func_impls.txt') or die $!;
	print scalar localtime();

	find_files(\&list_funcs, $path);
 
	print "\n";
	print scalar localtime();
	close IMPLS;
	system("start notepad func_impls.txt");
		
	sub list_funcs {
		my $file = shift;
		
		open(INFO, $file);		# Open the file
		my @lines = <INFO>;		# Read it into an array
		close(INFO);			# Close the file
		my $line;
		my @funcs;
		
		my $last = "";
                my $ind;
                my $count = @lines;
                for ($ind = 0; $ind < $count; $ind++)
		{
                        $line = $lines[$ind];
	  		if ($line =~ /(\w+)\s*\(.*\)/)
		  	{
				my $name = $1;
				next unless ($name =~ /[a-zA-Z]/);
				next if ($name =~ /^if$/);
				next if ($name =~ /^while$/);
				next if ($name =~ /^for$/);
				next if ($name =~ /^return$/);
				next if ($name =~ /^sizeof$/);
				next if ($name =~ /^switch$/);
				next if ($name =~ /^exit$/);
				next if ($name =~ /^int$/);
				next if ($line =~ /^\#\s*define/i);
				my $impl = "$last $line";
                                $impl = "$impl $lines[$ind+1]" if ($ind < ($count - 1));
				if ($impl =~ /\w+\*?\s+\*?\*?\s$name\s*\(.*\)\s+\{$/)
	  			{
					print IMPLS "$name\t$file\n";
				}
		  	}
		  	$last = $line;	
		}
	}

	sub find_files {
		my $callback = shift;
		my $path	 = shift;

		if (-d $path)
		{
		  # identify children
		  opendir DIR, $path or return;
		  my @files = readdir DIR;
		  closedir DIR;

		  # visit each child
		  foreach my $file (@files) {
			next if ($file =~ /^\.\.?$/);  # skip . and ..
			next if ($file =~ /^etc$/) || ($file =~ /^distrib$/) || ($file =~ /^CVS$/) || ($file =~ /^regress$/);
			unless (-d "$path/$file") {
				next unless ($file =~ /\.c$/i);
			}
			find_files($callback, "$path/$file");
		  }
		}
		else
		{
		   &$callback($path);
		}
	 }