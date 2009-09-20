#!/usr/bin/perl
    use strict; use warnings;
	my $src_path = shift;
	my $path = shift;
	die unless $src_path;
	die unless $path;
	open (IMPLS, "> $path/T5_Func_Source.txt") or die $!;
	print scalar localtime();

	find_files(\&list_funcs, $src_path);
 
	print "\n";
	print scalar localtime();
	close IMPLS;
	system("start notepad $path/T5_Func_Source.txt");
		
	sub list_funcs {
		my $file = shift;
		
		open(INFO, $file);		# Open the file
		my @lines = <INFO>;		# Read it into an array
		close(INFO);			# Close the file
		my $line;
		my @funcs;
		
		my $ind;
        my $count = @lines;
        for ($ind = 0; $ind < $count; $ind++)
		{
			$line = $lines[$ind];
            my $last = "";
            $last = $lines[$ind-1] if ($ind > 0);
            
	  		if ($line =~ /\w+\s*\(/)
		  	{
				my $impl = "$last $line";
				if ($impl =~ /^\s*\w+\*?\*?\s*\*?\*?\s+(\w+)\s*\(/)
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
				
	  				next if ($impl =~ /;/);
	  				
	  				my $i = 1;
	  				my $cont = 1;
	  				while (($ind + $i) < ($count - 1) && ($cont == 1))
	  				{
	  					$impl = "$impl $lines[$ind+$i]";
	  					$cont = 0 if ($impl =~ /;/);
	  					$cont = 0 if ($lines[$ind+$i] =~ /\(/);
	  					if (($cont == 1) && ($impl =~ /\)\s*\{\s*/))
	  					{
	  						print IMPLS "$name\t$file\n";
							$cont = 0;
						}
	  					$i++;
	  				}
				}
		  	}	
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