#!/usr/bin/perl -w
# ($Id)

# This file creates an index by scanning in list of gloss words
# and then scanning the tex file wrapping each of the words
# to be indexed with an index command.

# First parameter is the glossary file path
# The tex file is taken from STDIN and sent to STDOUT

$glosspath=$ARGV[0];
%gloss=();

open (GLOSS, $glosspath) || die "can't open glossary file";

while (<GLOSS>) {
    if (/^y\s+([\w-]*)\s+\d+\s*([^\s]*)/) {$gloss{lc $1} = defined $2 ? $2 : ""}
};

while (<STDIN>) {
    my $line=$_;
    my %iwords=();
    while ($line=~s/([\w]+(-[\w]+)*)//) {
	if (defined ($gloss{lc $1})) {
	    $iwords{$1} = $gloss{lc $1} unless (defined $iwords{$1});
	};
    };
    foreach $iword (keys %iwords) {
	s/([^\w-])$iword([^\w-])/$1$iword\\index{}$2/g}
    foreach $iword (keys %iwords) {
	$ie = ($gloss{lc $iword} eq "") ? lc $iword : $iwords{$iword};
# This following line causes indexed words to be emphasised in the body of the document
# This is to facilitate completion of the index prior to publication.
	s/$iword\\index{}/\\emph{$iword}\\index{$ie}/g}
# This line should be used when the emphasis is not required, i.e. for publication
#	s/$iword\\index{}/$iword\\index{$ie}/g}
    print 
};
