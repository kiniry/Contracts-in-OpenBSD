#!/usr/bin/perl
    use strict; use warnings;
    my $path = shift;
    die unless $path;
    open (LIST, 'count_filtered.txt') or die $!;
    open (IMPLS, 'func_impls.txt')  or die $!;
    open (FUNC_IMPLS, '> list_funcs_in_headers_filtered.txt')  or die $!;
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
       
       my @matches = grep(/$name\s+.+/, @impls);
       my $impl = $matches[0];
       print "$impl\n";
       $impl =~ /$name\s+(.+)/;
       
       print FUNC_IMPLS "$func\t$1\n";
    }
    print "\n";
    print scalar localtime();
    close FUNC_IMPLS;
    system("start notepad list_funcs_in_headers_filtered.txt");
   