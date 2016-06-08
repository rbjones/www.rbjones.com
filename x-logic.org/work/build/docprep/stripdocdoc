#!/usr/bin/perl -w
# $Id: stripdocdoc.pl,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $

# For stripping the documentation sections out of the ProofPower dtds to
# make the reference manual, and to prepare KWIC index.

# Command line parameters are:
# $ARGV[0] = filename prefix for individual pages of ref man
# $ARGV[1] = filename suffix for individual pages of ref man
# $ARGV[2] = filename for index
# rest = input dtd???.doc files

# kwic index is output to standard output.

$lib="\333";
$rib="\335";
$outfilenum=0;
$infilenum=2;
$outprefix=$ARGV[0];
$outsuffix=$ARGV[1];
$indexfile=$ARGV[2];

$lastparam=$#ARGV;

open (INDEX,"> $indexfile") || die "unable to create file $indexfile\n"; 

while($infilenum++ < $lastparam) {
    $infilename=$ARGV[$infilenum];
    open (INPUT, $infilename) || die "unable to open file $infilename\n";
    $_=<INPUT>;
    while ($_) {
	if (/^=DOC/) {
	    $outfilename=$outprefix.++$outfilenum.$outsuffix;
	    open (OUTPUT, "> $outfilename") || die "unable to create file $outfilename\n";
	    print OUTPUT "=XMLSTART\n";
	    while (!/^=ENDDOC/) {
		print OUTPUT;
		while (s/$lib([^$rib]+)$rib/$1/) {
		    $indexentry=$1;
		    if ($indexentry=~/\t/) {print STDERR "TAB IN:$_\n"}
		    else {print INDEX "$1\t$outfilenum\n"};
		    $firstpart="";
		    while($indexentry) {
			print "$indexentry\t$firstpart\t$outfilenum\n";
			$indexentry=~s/^([A-Za-z0-9]+_?|._?)//;
			$firstpart.=$1;
		    };
		};
		$_=<INPUT>;
	    };
	    print OUTPUT;
	    print OUTPUT "=XMLEND\n";
	    close OUTPUT;
	    };
	$_=<INPUT>;
    };
};

close INPUT;
close INDEX;
