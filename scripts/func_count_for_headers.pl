#!/usr/bin/perl
    use strict; use warnings;
    my $path = shift;
    die unless $path;
    open (LIST, 'list_funcs.txt') or die $!;
    open (CALLS, 'func_calls.txt')  or die $!;
    open (COUNTS, '> detailed.txt')  or die $!;
    print scalar localtime();
    my @funcs = <LIST>;	
    close(LIST);			
    my @calls = <CALLS>;	
    close(CALLS);			

    my $func;
    foreach $func (@funcs)
    {
         
       $func =~ s/\n//g;
       my ($header, $name) = split(/\s/, $func);
       my @matches = grep(/$name/, @calls);
       my $count = @matches;
       print COUNTS "$count\t$func\n";
    }
    print "\n";
    print scalar localtime();
    close COUNTS;
    system("start notepad detailed.txt");
   