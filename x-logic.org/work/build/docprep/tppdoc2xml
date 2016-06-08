#!/usr/bin/perl -w
# $Id: tppdoc2xml.pl,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $
# for translating unsupported character codes in a ProofPower document into entities.
# Translates from standard input to standard output.

use XLogic::xpptran;

$_=<STDIN>;
L: while ($_){
	$_=&XLogic::xpptran::tranppdoc2xml_nft($_);
	print;
	$_=<STDIN>;
};
