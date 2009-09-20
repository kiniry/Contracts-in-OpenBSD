#!/usr/bin/perl
    use strict; use warnings;
    my $src_path = shift;
    my $path = shift;
    die unless $path;
    die unless $src_path;
    open (CALLS, "> $path/T2_FuncCallee.txt") or die $!;
    print scalar localtime();
			
    find_files(\&list_funcs, $src_path);
 
    print "\n";
    print scalar localtime();
    close CALLS;
    system("start notepad $path/T2_FuncCallee.txt");
        
    sub list_funcs {
        my $file = shift;
		open(INFO, $file);		# Open the file
		my @lines = <INFO>;		# Read it into an array
		close(INFO);			# Close the file
        my $line;
        my @funcs;
        my $comment = 0;
        my $count = @lines;
		for (my $ind = 0; $ind < $count; $ind++)
		{
			$line = $lines[$ind];
			if ($comment == 1)
			{
				$comment = 0 if $line =~ /\*\/\s*$/;
				next;
			}
			elsif ($line =~ /^\s*\/\*/) 
			{
				$comment = 1 unless ($line =~ /\*\/\s*$/);
				next;
			}
			if ($line =~ /[\W\s]\w+\s*\(/)
          	{
          		next if $line =~ /^extern/;
	  			my $impl = $line;
	  			$impl = "$lines[$ind-1] $impl" if ($ind > 0);
  				next if $impl=~ /\s*\w+\*?\*?\s*\*?\*?\s+\w+\s*\(/;
  				while ($line =~ /[\W\s](\w+)\s*\(/)
          		{
            		my $name = $1;
            		$line =~ s/$name//;
					next unless ($name =~ /[a-zA-Z]/);
                	next if ($name =~ /^if$/);
                	next if ($name =~ /^while$/);
                	next if ($name =~ /^for$/);
                	next if ($name =~ /^return$/);
                	next if ($name =~ /^sizeof$/);
                	next if ($name =~ /^switch$/);
                	next if ($name =~ /^exit$/);
                	next if ($name =~ /^int$/);
                	next if ($name =~ /^else$/);

                	print CALLS "$name\n";   
          		}
          	}
  		}
    }

    sub find_files {
        my $callback = shift;
        my $path     = shift;

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