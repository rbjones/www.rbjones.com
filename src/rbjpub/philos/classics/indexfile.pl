#!/usr/bin/perl -w
# ($Id)

# This file creates an index by scanning in list of index words
# and then scanning the tex file wrapping each of the words
# to be indexed with an index command.

# First parameter is the indexary file path
# The tex file is taken from STDIN and sent to STDOUT

$indexpath=$ARGV[0];
%index=();

open (GLOSS, $indexpath) || die "can't open index file";

while (<GLOSS>) {
    if (/^y\s+([\w-]*)\s+\d+/) {$index{$1}=2}
};

while (<STDIN>) {
    my $line=$_;
    my %iwords=();
    while ($line=~s/([\w]+(-[\w]+)*)//) {if (defined ($index{lc $1})) {$iwords{$1}="$1\\index{}"}};
    foreach $iword (keys %iwords) {
	s/([^\w-])$iword([^\w-])/$1$iword\\index{}$2/g;
	$lciw=lc $iword;
	s/$iword\\index{}/$iword\\index{$lciw}/g}
    print 
};
