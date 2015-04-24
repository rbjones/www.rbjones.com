#!/bin/perl -w
use strict;
use Data::Dumper;
use FileHandle;

my $file = "data.out";

{
    my(%hash);

    $hash{key1} = [ 1, "b", "c" ];
    $hash{key2} = [ 4.56, "g", "2008-12-16 19:10 -08:00" ];

    my $str = Data::Dumper->Dump([ \%hash ], [ '$hashref' ]);
    print "Output: $str";

    my($out) = new FileHandle ">$file";
    print $out $str;
    close $out;
}

{
    my($in) = new FileHandle "<$file";
    local($/) = "";
    my($str) = <$in>;
    close $in;

    print "Input: $str";

    my($hashref);
    eval $str;
    my(%hash) = %$hashref;

    foreach my $key (sort keys %hash)
    {
        print "$key: @{$hash{$key}}\n";
    }
}
