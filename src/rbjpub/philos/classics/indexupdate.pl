#!/usr/bin/perl -w
# ($Id: indexupdate.pl,v 1.1 2013/02/23 17:13:41 rbj Exp $)

# This file takes an index file and merges into it an up-to-date list of candidates.

# First parameter is the glossary file path.
# Second parameter is the path for a file of additional words.
# The merged files are output to STDOUT.

# The merged files contain all the lines in the glossary index which begin with a character
# other than white space, together with one line for each of the additional words which
# does not appear in the glossary in a line beginning with a non-white-space character.

$glosspath=$ARGV[0];
$newwords=$ARGV[1];

%gloss=();

open (GLOSS, $glosspath) || die "can't open glossary file";

while (<GLOSS>) {
    if (/^(\w)\s+([\w-]*)\s+(\d+)\s*([^\s]*)/) {
	$gloss{lc $2} = {flag => $1, count => $3, entry => $4}
    }
};



open (NEW, $newwords) || die "can't open new words file";

while (<NEW>) {
    if (/^\s+([\w-]*)\s+(\d+)/) {
	if (!defined($gloss{lc $1})) {
	    $gloss{lc $1} = {flag => "", count => $2, entry => ""}}
	else {
	    $gloss{lc $1} {count} = $2
	}
    }    
};

@sortkeys= sort(keys(%gloss));

foreach (@sortkeys) {
    $key=$_;
    $flag = $gloss{$key}{'flag'}; 
    $pkey=sprintf('%-25s', $key);
    $count = $gloss{$key}{'count'}; 
    $entry = $gloss{$key}{'entry'}; 
    print "$flag\t$pkey\t$count\t$entry\n";
}
