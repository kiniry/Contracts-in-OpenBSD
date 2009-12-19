#!/usr/bin/perl
    use strict; use warnings;
    my $src_path = shift;
    my $path = shift;
    die unless $path;
    die unless $src_path;
    open (LIST_FUNCS, "> $path/T1_HeaderName_FuncName.txt") or die $!;
    open(HEADER_FOLDERS, "$path/T0_HeaderFolders.txt")  or die $!;
    my @folders = <HEADER_FOLDERS>;	
    close(HEADER_FOLDERS);			
    print scalar localtime();

    my $folder;
    foreach $folder (@folders)
    {
      $folder =~ s/\s//g;
      my @headers = find_files(\&is_filtered_Header, "$src_path/$folder");
      my $header;
      foreach $header (@headers)
      {
        my @funcs = list_funcs($header);
        my $func;
        
        foreach $func (@funcs)
        {
          print "\n$header\t$func\n";
          print LIST_FUNCS "$header\t$func\n";
        }
      }
    }
    print "\n";
    print scalar localtime();
    close LIST_FUNCS;
    system("start notepad $path/T1_HeaderName_FuncName.txt");

    sub is_filtered_Header {
        my $file = shift;
        return 0 if (-d $file);
        return 1 if ($file =~ /\.h$/);
        return 0;
    }

    
    sub list_funcs {
        my $file = shift;
        open(INFO, $file);		# Open the file
		my @lines = <INFO>;		# Read it into an array
		close(INFO);			# Close the file
        my $line;
        my @funcs;
		foreach $line (@lines)
		{
  	  		if ($line =~ /^\s*\w+\*?\s+\*?\*?(\w+)\s*\((.*)\)/)
          	{
            	push @funcs, $1  unless ($line =~ /\)\(/) || ($2 =~ /\"/) || ($2 =~ /\(/) || ($line =~ /\(\*/); 
          	}
  		}
        return @funcs;
    }

    sub find_files {
        my $callback = shift;
        my $path     = shift;

        my @retval;

        push   @retval, $path if &$callback($path);
        return @retval unless (-d $path);

        # identify children
        opendir DIR, $path or return;
        my @files = readdir DIR;
        closedir DIR;

        # visit each child
        foreach my $file (@files) {
            next if ($file =~ /^\.\.?$/);  # skip . and ..
            push @retval, find_files($callback, "$path/$file");
        }

        return @retval;
    }