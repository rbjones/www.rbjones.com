#!/usr/bin/perl -w
# $Id: xxml2xml.pl,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $
# for translating unsupported entities in an XML file into images.
# Translates from standard input to standard output.

use XLogic::xpptran;

$_=<STDIN>;
L: while ($_){
	$_=&XLogic::xpptran::tranxxml2xml($_);
	print;
	$_=<STDIN>;
};
