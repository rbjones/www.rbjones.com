#!/usr/bin/perl -w
# for extracting titles and abstracts from a collection of LaTeX
# documents and creating an list of abstracts in XML.

# parameters: input files names
# output to standard output.

# use XLogic::xpptran;

#$true=1;
#$false=0;

$title=""; $abstract=""; $pdfname="";

$filecount=$#ARGV;
$ssc=2;
$lhscolcount=$ARGV[0];
$pdfprefix=$ARGV[1];
if ($lhscolcount==0) {$lhscolcount=int($filecount/2)+1};

fileloop: while ($ssc <= $filecount) { 
    $title=""; $abstract=""; $pdfname="";
    $filename=$ARGV[$ssc];
    open INPUT, $filename || die "unable to open file $filename";
    $pdfname=$filename;
    $pdfname=~s/\.tex//;
    while(<INPUT>){
	if (/(pdftitle=|title)\{([^}]*)\}/) {if($title eq "") {$title=$2}}
        elsif (/pdfname\{([^}]*)\}/) {$pdfname=$1}
        elsif (/\\begin\{abstract\}/) {
	    $abstract="";
	    $_=<INPUT>;
	    until (/\\end\{abstract\}/) {s/^\%(.*)$/$1/; $abstract.=$_; $_=<INPUT>};
	    print "<subsec title=\"$pdfname - $title\"";
            if ($pdfname) {print " href=\"$pdfprefix$pdfname\.pdf\"\n"};
	    print ">\n";
            print "$abstract";
            print "</subsec>\n";
	    if ($ssc == $lhscolcount) {print "</sbcol><sbcol>\n"};
	    $ssc+=1;
            next fileloop;
        };
    };
};
