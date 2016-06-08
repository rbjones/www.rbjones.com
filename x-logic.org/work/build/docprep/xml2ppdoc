#!/usr/bin/perl -w
# $Id: xml2ppdoc.pl,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $
# for translating an XML file to a  ProofPower ".doc" file.
# Translates from standard input to standard output.

use XLogic::xpptran;

$box="\260";
$predbar="\367";
$s="\271";
$holconst=$s."HOLCONST\n";
$lang="XML";

$start="=XML\n";
$_=<STDIN>;
L: while ($_){
	if (/^<ft\s+lang="xl-([^\"]*)".*>/){
		$start="=\U$1\E\n";
		$lang=$1;
   	}
	elsif (/^<\/ft>/){
		$start="=XML\n";
		$lang="XML";
	}
	elsif (/^<holconst><holsig>/){
		&doholconst;
		$start="=XML\n";
		$lang="XML";
	}
	else {
        if ($start) {
			print $start;
			$start="";
		};
		if ($lang eq "XML"){$_=&XLogic::xpptran::tranxml2ppdoc_nft($_)}
		else {$_=&XLogic::xpptran::tranxml2ppdoc($_)};
		print;
	};
	$_=<STDIN>;
};

sub doholconst {
	print $holconst;
	$_=<STDIN>;
	while (!/<\/holsig>/){
        $_=&XLogic::xpptran::tranxml2ppdoc($_);
		print;
		$_=<STDIN>;
	}
	$_=<STDIN>;
	if (/<holpred>/) {
		$_=<STDIN>;
		print $predbar."\n";
		while (!/<\/holpred>/){
			$_=&XLogic::xpptran::tranxml2ppdoc($_);
			print;
			$_=<STDIN>;
		};
		$_=<STDIN>
	};
	if (/^<\/holconst>$/) {print $box."\n"}
	else {print "end of holconst not found\n"};
};




