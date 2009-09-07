#!/usr/bin/perl
    use strict; use warnings;
    my $path = shift;
    die unless $path;
    open (CALLS, '> func_calls.txt') or die $!;
    print scalar localtime();

    find_files(\&list_funcs, $path);
 
    print "\n";
    print scalar localtime();
    close CALLS;
    system("start notepad func_calls.txt");
    

    
    sub list_funcs {
        my $file = shift;
        
        open(INFO, $file);		# Open the file
	my @lines = <INFO>;		# Read it into an array
	close(INFO);			# Close the file
        my $line;
        my @funcs;
	foreach $line (@lines)
	{
          if ($line =~ /\W+(\w+)\s*\((.*)\).*[\);]/)
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

                print CALLS "$name\n";   
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