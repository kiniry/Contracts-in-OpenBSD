#!/usr/bin/perl
    use strict; use warnings;
    my $path = shift;
    die unless $path;
    find_files("$path/share/man");
    print "\n";
   
  sub list_includes {
        my $file = shift;
        open(INFO, $file);		# Open the file
		my @lines = <INFO>;		# Read it into an array
		close(INFO);			# Close the file
        my $line;
        my @funcs;
		foreach $line (@lines)
		{
  	  		if ($line =~ /(\#include.*\.h\>)/)
          	{
            	print "\n$1";
          	}
  		}
    }


   sub find_files {
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
         	   	find_files("$path/$file");
        	}
        }
        else
		{
			list_includes($path);
		}
    }

