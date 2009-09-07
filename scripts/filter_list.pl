#!/usr/bin/perl
    use strict; use warnings;
    my $detailed_txt_path = shift;
    die unless $detailed_txt_path;
    open (FILTERED, '> filtered.txt') or die $!;
    open (DETAILED_COUNT, "$detailed_txt_path/list_funcs_in_headers_filtered.txt")  or die $!;
    my @funcs = <DETAILED_COUNT>;	
    close(DETAILED_COUNT);			
    print scalar localtime();

    my $func;
    foreach $func (@funcs)
    {
      $func =~ s/\n//g;
      my ($count, $header, $funcn, $file) = split(/\s/, $func);
      my $ret = checks($file);
 
      if ($ret == -1)
      {
       print FILTERED "?\t$func\n";
      }
      elsif ($ret == 1) 
      { 
       print FILTERED "+\t$func\n"; 
      }
      else
      {
        print FILTERED "!\t$func\n";
      }
    }

    print "\n";
    print scalar localtime();
    
    close FILTERED;
    close DETAILED_COUNT;
    system("start notepad filtered.txt");
    
    sub checks
    {
      my $file = shift;
      
      open (IMPL, $file) or return -1;
      
      my @lines = <IMPL>;
      
      my $line;
      foreach $line (@lines)
      {
          if (  ($line =~ /goto\s+\w+;/)  
             || ($line =~ /\(\*\w+\)\(.*\)/)
             || ($line =~ /\(\w+\s*\*\)/)
             || ($line =~ /union/)
             || ($line =~ /\(.*,\s*\.\.\.\)/)
             )
          {
		close IMPL;
                return 0;
          }
      }
      close IMPL;
      return 1;
    }
    