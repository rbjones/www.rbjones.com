#!/usr/bin/perl -w
# ($Id)
# For preprocessing an XML file containing xld:ft sections before
# transforming into XHTML using XT.
# Adds a <ftbr /> tag at the end of each line in a formal text section.
# This second version does not make use of XML::DOM and has been done because I had a problem
# getting a working installation of XML::DOM on OS X.

# This procedure copies standard input to standard output until it finds a formal text element.
sub skiptoft {
    if (!eof(STDIN)) {
	$_=<STDIN>;
	while (!eof(STDIN) && !/^\W*\<(ft|hosig|holpred)/){
	    print;
	    $_=<STDIN>
	};
	print
    };
};

# This procedure copies formal text from STDIN to STDOUT until it finds a formal text end tag. 
sub transcribeft {
    $_=<STDIN>;
    while (!eof(STDIN) && !/^\<\/(ft|holsig|holpred)\>/){
	s!\t!<fttab \/>!g;
	s/^(.*)$/$1<ftbr \/>/;
	print;
	$_=<STDIN>
    };
    unless (eof(STDIN)){print}
};

$_=<STDIN>;
while(!eof(STDIN)){
    &skiptoft;
    &transcribeft;
};
