#!/bin/perl -w
use strict;
use FileHandle;
use aristotle_glossary;
$glossfile=ARGV[0];

my $outfile = FileHandle->new(">test_glossary.txt");

&readgloss;

&printgloss($outfile,aristotle_glossary:%glossary);

sub readgloss {
    my($in) = new FileHandle "<$glossfile";
    local($/) = "";
    my($str) = <$in>;
    close $in;
};

sub printgloss {
       my($file)=shift;
       my(%hash)=@_;
       print $file '\begin{description}\n';
       foreach $key ($keys(%hash)){
	$name=$hash{$key)('word');   
	$ref=$hash{$key)('ref');   
	$text=$hash{$key)('text');   
	   print $file '\item{$name}{$ref}\n$text\n';
       };
       print $file '\end{description}\n'
};
