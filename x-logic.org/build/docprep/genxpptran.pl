#!/usr/bin/perl
# $Id: genxpptran.pl,v 1.2 2010-01-25 12:53:11 rbj Exp $
# a script to generate a translate procedure for non-ascii characters inserted by xpp
# read the table of characters accepted from ppcodes.doc.
# parameters required are:
# 1. file containing table of character translations

$infile=$ARGV[0];
$outfile="xpptran.pm";

# open codes table
open (INPUT, $infile) || die "unable to open file: $infile\n";
# skip notes before table
$_=<INPUT>;
while(!/^=/){$_=<INPUT>};

#output a perl module called xpptran.pm

open (OUTPUT, "> $outfile") || die "unable to create file: $outfile\n";

	 print OUTPUT <<EOF;
#!/usr/local/bin/perl
#translate routine to translate non-ascii characters into xml (mostly xhtml) entities

package XLogic::xpptran;

sub tranppdoc2xml {
	my(\$line)=\@_;
	\$_=\$line;
# first process the &, < and > chars
	s/&/&amp;/g;
	s/</&lt;/g;
	s/>/&gt;/g;
	\$line=&tranppdoc2xml_nft(\$_);
};

sub tranppdoc2xml_nft {
	my(\$line)=\@_;
	\$_=\$line;
# first process the subscript/superscript characters
    s/\\211(.)/<sub>\$1<\\\/sub>/g;
    s/\\233(.)/<sup>\$1<\\\/sup>/g;
    s/\\347([^\\352]*)\\352/<sup class="l">\$1<\\\/sup>/g;
    s/\\350([^\\352]*)\\352/<sub class="l">\$1<\\\/sub>/g;
# then specific translations for each non-standard character
EOF

# now we generate substitute commands for the rest.
	while (<INPUT>) {
		if    (/^(.)\t+(\S+)\t+(\S+)\t+(\S+)/) {
			my($code,$unicode,$entity,$gif,$ename)=($1,$2,$3,$4,$3);
			if ($ename eq "!") {$ename = "$gif"}; 
			if ($ename eq "!") {$ename = "#x$unicode"}; 
			if ($ename eq "#x!") {$ename = "#".(sprintf "%o", ord($code))}; 
			$subc="s/\\".(sprintf "%o", ord($code))."/&$ename;/g;";
			print OUTPUT "\t$subc\n"
			}
};
	print OUTPUT <<EOF;
	\$line=\$_};

sub tranxml2ppdoc {
	my(\$line)=\@_;
	\$_=\$line;
# first process the &, < and > chars
	s/&lt;/</g;
	s/&gt;/>/g;
	s/&amp;/&/g;
# add a manual entry for equiv

	\$line=&tranxml2ppdoc_nft(\$_);
};

sub tranxml2ppdoc_nft {
	my(\$line)=\@_;
	\$_=\$line;
# first process single subscripted characters
	s/<sub>(.)<\\\/sub>/\\211\$1/g;
	s/<sup class="l">([^<]*)<\\\/sup>/\\347\$1\\352/g;
	s/<sub class="l">([^<]*)<\\\/sub>/\\350\$1\\352/g;
# then process &#n; forms for <3 digits in n
	while(/\\&\\\#(\\d\\d?\\d?);/){my \$pat="\\\\\$1"; \$pat=eval("\\\"\$pat\\\""); s/\\&\\\#\$1;/\$pat/};
# then the rest of the specific translations
EOF

# now we generate substitute commands for the rest.
	close INPUT;
	open (INPUT, $infile) || die "unable to open file: $infile\n";
# skip notes before table
	$_=<INPUT>;
	while(!/^=/){$_=<INPUT>};
	while (<INPUT>) {
		if    (/^(.)\t+(\S+)\t+(\S+)\t+(\S+)/) {
			my($code,$unicode,$entity,$gif,$ename)=($1,$2,$3,$4,$3);
			if ($ename eq "!") {$ename = "$gif"}; 
			if ($ename eq "!") {$ename = "#$unicode"}; 
			if ($ename eq "!") {next}; 
			$subc="s/&$ename;/\\".(sprintf "%o", ord($1))."/g;";
			print OUTPUT "\t$subc\n"
		};
	};
	print OUTPUT "\ts/&equiv;/\\244/g;\n";
	print OUTPUT <<EOF;
	\$line=\$_};

sub tranxxml2xml {
	my(\$line)=\@_;
	\$_=\$line;
EOF
# now we generate substitute commands for the rest.
	close INPUT;
	open (INPUT, $infile) || die "unable to open file: $infile\n";
# skip notes before table
	$_=<INPUT>;
	while(!/^=/){$_=<INPUT>};
	while (<INPUT>) {
		if (/^(.)\t+(\S+)\t+(\S+)\t+(\S+)/) {
			my($code,$unicode,$entity,$gif,$ename)=($1,$2,$3,$4,$3);
			if ($ename eq "!") {$ename = "$gif"}; 
			if ($ename eq "!") {next};
			if ($unicode eq "!" && $entity eq "!") {
			    $subc="s/\\&$ename;/<sg name=\"$gif.gif\"\\/>/g;";
			    print OUTPUT "\t$subc\n";
			    next
			}
			else {if ($unicode eq "!") {
			    $subc="s/\\&$ename;/&#x$unicode;/g;";
			    print OUTPUT "\t$subc\n"
			      }
			};
		    }
	    };
	print OUTPUT <<EOF;
	\$line=\$_};

1;
EOF









