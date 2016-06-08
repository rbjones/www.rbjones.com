#!/usr/bin/perl -w
# $Id: ppdoc2xml.pl,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $
# for translating a ProofPower ".doc" file into XML.
# Translates from standard input to standard output.
# If the file does not begin with an =XML section a header and tail
# are included using information supplied on the argument line as follows:
# argv[0] = name

use XLogic::xpptran;

$box="\260";
$predbar="\367";
$s="\271";

$name=$ARGV[0];
$root=$ARGV[1];

$true=1;
$false=0;
$start="<ft lang=\"xl-tex\">\n";
$lang="TEX";
$finish="";
$inppDOC=$false;
$_=<STDIN>;
if (!/=XML/) {
	print <<End;
<?xml version="1.0"?>
<!DOCTYPE ProofPower SYSTEM "pp-symbol.ent">
<xldoc xmlns="http://www.x-logic.org/xmlns/draft/xld"
       xmlns:xhtml="http://www.w3.org/TR/xhtml1/strict"
	   name="$name"
	   root="$root"
	   class="con"
       up="../index.html"
       rbjhome="http://www.rbjones.com/rbjpub/rbj.htm">
End
};
L: while ($_){
	if (/^=(\S+)(.*)/){
		if ($finish && ! $start) {print $finish; $finish=""};
		$lang=$1;
		if ($lang eq "XML") {
			$start="";
			$finish="";
		}
		elsif ($lang eq "DOC") {
		    if ($inppDOC) {
			print "</pp:doc>\n";
		    };
		    print "<pp:doc>\n";
		    $inppDOC=$true;
		    $start="<pp:$lang>\n<ft lang=\"xl-sml\">\n";
		    $finish="</ft>\n</pp:$lang>\n";
                }
		elsif ($lang eq "FAILURE"
                      || $lang eq "EXAMPLE"
                      || $lang eq "USES") {
		    if (! $inppDOC) {
			print "<pp:doc>\n";
			$inppDOC=$true;
		    };
		    $start="<pp:$lang>\n<ft lang=\"xl-\L$lang\E\">\n";
		    $finish="</ft>\n</pp:$lang>\n";
                }
                elsif ($lang eq "SYNOPSIS"
                      || $lang eq "DESCRIBE"
                      || $lang eq "FAILUREC"
                      || $lang eq "COMMENTS"
                      || $lang eq "SEEALSO"
                      || $lang eq "KEYWORDS") { 
		    if (! $inppDOC) {
			print "<pp:doc>\n";
			$inppDOC=$true;
		    };
		    $start="<pp:$lang>\n";
		    $finish="</pp:$lang>\n";
                }
                elsif ($lang eq "ENDDOC") {
		    print "$finish</pp:doc>\n";
		    $inppDOC=$false;
		    $lang="TEX";
		    $start= "<ft lang=\"xl-tex\">\n";
		    $finish="</ft>\n";
		}
                else {
                    if ($inppDOC) {
			print "$finish</pp:doc>\n";
			$inppDOC=$false;
		    };
		    $start= "<ft lang=\"xl-\L$1\E\" rest=\"$2\">\n";
		    $finish="</ft>\n";
		};			
	}
	elsif (/^($s)HOLCONST(.*)/){
		if ($finish && ! $start) {print $finish};
		$start="";
		print "<holconst><holsig>\n";
		$lang="holsig";
		$finish="</holsig>\n";
	}
	elsif (/^$predbar(.*)/ && $lang eq "holsig"){
		print "</holsig>\n<holpred>\n";
		$lang="holpred";
		$start="";
		$finish="</holpred>\n";
	}
	elsif (/^$box/ && ($lang eq "holsig" || $lang eq "holpred")) {
		print $finish;
		print "</holconst>\n";
		$start="";
		$finish="";
		$_="=TEX\n"; next L}
	else {
        if ($start) {
			if (/^\s*$/) {$start.=$_; $_=<STDIN>; next L}
			else {
				print $start;
				$start="";
			};
		};
		if ($lang ne "XML") {
			$_=&XLogic::xpptran::tranppdoc2xml($_);
		}
		else {
			$_=&XLogic::xpptran::tranppdoc2xml_nft($_);
		};
		print;
	};
	$_=<STDIN>;
};
	if ($lang ne "XML"){print "$finish</xldoc>\n"};


#sub copysection {
#	$_=<STDIN>;
#	while (!/^(=|$s|$box|$predbar)/){
#        if ($lang eq "XML") {$_=&XLogic::xpptran::tranppdoc2xml_nft($_)}
#        else {$_=&XLogic::xpptran::tranppdoc2xml($_)};
#		print;
#		$_=<STDIN>;
#	}
#};












