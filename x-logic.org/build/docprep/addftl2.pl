#!/usr/bin/perl -w
# ($Id)
# For preprocessing an XML file containing xld:ft sections before
# transforming into XHTML using XT.
# Encloses each line in formal text sections with <xld:ftl></xld:ftl> markers.
# This second version does not make use of XML::DOM and has been done because I had a problem
# getting a working installation of XML::DOM on OS X.

# This procedure copies standard input to standard output until it finds a formal text element.
sub skiptoft {
    while (!eof(STDIN) && !/^\W*\<(ft|hosig|holpred)/){
	print;
	$_=<STDIN>
    };
};

# This procedure copies formal text from STDIN to STDOUT until it finds a formal text end tag. 
sub transcribeft {
    while (!eof(STDIN) && !/^\<\/(ft|holsig|holpred)\>/){
	s!\t!<fttab \/>!g;
	s/^(.*)$/\1<ftnl \/>/;
	print;
	$_=<STDIN>
    };
};

$_=<STDIN>;
while(!eof(STDIN)){
    &skiptoft;
    print;
    $_=<STDIN>;
    &transcribeft;
    print;
    $_=<STDIN>
};
