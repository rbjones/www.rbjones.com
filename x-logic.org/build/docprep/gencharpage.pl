#!/usr/bin/perl
# $Id: gencharpage.pl,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $
# a script to generate an html ProofPower character page from ppcodes.doc
# (or similar) and a table of entities (from pp-symbol.ent or similar).
# 
# parameters required are:
# 1. file containing table of character info (ppcodes.doc probably!)
# 2. output filename
# 3. the name of an entitiy file for listing
# 4. the relative path to the image directory (sg)

$infile=$ARGV[0];
$outfile=$ARGV[1];
$infile2=$ARGV[2];
$imagepath=$ARGV[3];

# open codes table
open (INPUT, $infile) || die "unable to open file: $infile\n";
# skip notes before table
$_=<INPUT>;
while(!/^=/){$_=<INPUT>};

#output a page of HTML4

open (OUTPUT, "> $outfile") || die "unable to create file: $outfile\n";

print OUTPUT <<EOF;
<HTML>
<HEAD><TITLE>ProofPower Special Character Table</TITLE></HEAD>
<BODY BGCOLOR="#ddeeff">
This table shows information about the rendering of the ProofPower special characters in HTML.
<p>
ProofPower uses a special 8-bit character set in which the characters below 128 are ascii and those above are a special encoding of a suitable selection of logical or mathematical characters, many of them to represent the characters used in the Z specification language.
<p>
ProofPower comes with support for editing documents encoded in this way suitable for providing specification and proof scripts which can be processed by ProofPower, and for processing these documents using LaTeX to give postscript or PDF files.
It does not come with any support for rendering such documents in HTML.
The RBJones.com web site does make use of documents which are prepared in XML for processing by ProofPower and for presentation via HTML.
This was a hack supporting only the subset of characters which happen to have been needed for the material used at RBJones.com, rather than a full implementation of HTML support for ProofPower sources, however, it is gradually getting more comprehensive.
<P>
The following table has been prepared to assist in occasional enhancement of this hack and shows which of the ProofPower special characters can be rendered in HTML by each of three methods.
<P>
The three methods are:
<UL>
<LI>using small images (gifs in fact)
<LI>using HTML4 entities
<LI>using the UNICODE character code (in the form &amp;#xdddd;)
</UL>
It would also be possible to select characters from named fonts, but success would depend on what fonts were available on the machine on which the browser was running, so I didn't think this line worth investigating.

The present translation algorithms use the first method whenever an image is available, because the other two methods work only on some browsers.
If no image is available the bald UNICODE character code is used, because inspection of results on a random selection of browsers suggests that the UNICODE character codes are implemented whenever the corresponding HTML4 entity is but not always vice-versa.

Below is also presented <A HREF="#pps">information from pp-symbol.ent</A> which consists of the entitiy definitions required for processing XML files including ProofPower source used to generate this web site.

<CENTER><TABLE><CAPTION><B>ProofPower Special Character Renderings</B></CAPTION>
<TR><TD><B>code</B></TD><TD><B>gif</B></TD><TD WIDTH=40><B></B></TD><TD><B>entity</B></TD><TD><B></B></TD><TD><B>unicode</B></TD><TD><B></B></TD><TD><B></B></TD></TR>
EOF

# now we generate substitute commands for the rest.
while (<INPUT>) {
	if    (/^(.)\t+(\S+)\t+(\S+)\t+(\S+)\t+(\S+)\t+(.*)/) {
		my($code,$unicode,$entity,$gif,$htmle,$comment)=($1,$2,$3,$4,$5,$6);
		$cdisp=sprintf "%o", ord($code);
		my($ucdisp,$gifdisp,$edisp)=("&nbsp;","&nbsp;","&nbsp;");
		if ($unicode ne "!") {$ucdisp = "&#x$unicode;"};
		if ($gif ne "!") {$gifdisp = "<IMG SRC=\"$imagepath$gif.gif\">"}; 
		if ($htmle ne "!") {$edisp = "&$htmle;"}; 
		print OUTPUT <<EOF
<TR><TD>$cdisp</TD><TD>$gif</TD><TD>$gifdisp</TD><TD>$htmle</TD><TD>$edisp</TD><TD>$unicode</TD><TD>$ucdisp</TD><TD>$comment</TD></TR>
EOF
                };
};
print OUTPUT <<EOF;
</TABLE></CENTER>
EOF
close INPUT;
open (INPUT2, $infile2) || die "unable to open file: $infile2\n";
# skip lines not defining entities
$_=<INPUT2>;
				      print OUTPUT <<EOF;
<P>
<A NAME="pps"></A>
The following table shows the character entities used in XML source for ProofPower pages on this site.
This is in fact the HTML4 entities plus entities for some of the ProofPower symbols which don't appear in HTML4.
Not all of these have sensible values, when there is no corresponding UNICODE character or when I just havn't found it yet, and even where I have identified a UNICODE character it is likely not to display correctly in HTML.
The ProofPower special entities come first, followed by the HTML4 entities (of which the first is "nbsp").

<CENTER>
<TABLE><CAPTION><B>Listing of Entities in $infile2</B></CAPTION>
EOF

while(<INPUT2>){
    if (/<!ENTITY\s+(\S+)[^"]*"\&([^;]*)\;\"> <!--(.*)/){
        my($ename2,$ecode2,$ecomment2)=($1,$2,$3);
        print OUTPUT <<EOF
<TR><TD>$ename2</TD><TD>$ecode2</TD><TD>&$ecode2;</TD><TD>$ecomment2</TD></TR>
EOF
    };
};

print OUTPUT <<EOF;
</TABLE>
</BODY>
</HTML>
EOF
    close INPUT2;
    close OUTPUT;

