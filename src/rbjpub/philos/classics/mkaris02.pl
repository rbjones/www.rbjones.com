#!/usr/bin/perl -w

$Id="\$Id";
$modified="2009/04/26";
$created="1996/11/24";

# The following kinds of files are created by the subroutines below:
# (1) Overall index with one entry per file or book (some files are
# 	a single book, some multiple books).
# (2) Part indexes for each book
# (3) Paragraph indexes for each Part
# (4) Part (HTML) files containing the text of the work
# (5) A book tex file to make a book PDF.

# file naming conventions are:
# (1) every file begins with $stub (set in main procedure)
# (2) overall index is $stub."index.htm"
#$index=$stub."index.htm";
# (3) file numbers ($file) are one digit
# (4) Book numbers are one digit ($book).
#		The index of parts in a book is called $stub.$file.$book.".htm"
# (5) Part numbers are two digit ($part)
#		The index of paragraphs in a part is called $stub.$file.$book.$part.".htm"
#		The content of a part is called $stub.$file.$book.$part."c.htm"
# (6) The last character of the filename is "c" for content and "i" for an index.
# (7) The tex files are $stub.tex

# The tex files are structured using the following commands which should be defined in
# a tex wrapper which includes the generated tex file.
# \Avolume   =?> part
# \ASbook    =?> chapter
# \AMbook    =?> chapter
# \Apart     =?> section

$rbjgifs="../../../../rbjgifs";
$rbjhref="<A HREF=\"../../../rbj.htm\">";
$rbjimg="<IMG SRC=\"$rbjgifs/rbjin1.gif\" ALT=RBJ ALIGN=TOP BORDER=0>";
$homeimg="<IMG SRC=\"$rbjgifs/home.gif\" ALT=HOME BORDER=0>";
$upimg="<IMG SRC=\"$rbjgifs/up.gif\" ALT=UP BORDER=0 ALIGN=LEFT>";
$upimgm="<IMG SRC=\"$rbjgifs/up.gif\" ALT=UP BORDER=0>";
$rbjsig="$rbjhref$rbjimg</A>";
$homeref="<A HREF=\"../../../index.htm\">";
$upref="<A HREF=\"../index.htm\">";
$home="$homeref$homeimg</A>";
$up="$upref$upimg</A>";
$upm="$upref$upimgm</A>";
$body="<BODY BGCOLOR=\"#e0e0f0\">";
$pre=0; # this flag indicates whether we are in a <PRE>/\verbatim section
$precount=0; # this flag indicates how many PRE sections have been processed
%pretexts=(); # this hash contains the tex source to replace the contents of the PRE sections
%greek2tex=(); # this maps the utf8 greek words used in the texts into tex.
%greek2htm=(); # this maps the utf8 greek words used in the texts into html.

$pretexts{1}=<<EOF;

\\vspace{1em}
\\hfil
\\begin{tabular}{c c c}
{\\bf A. Affirmation} && {\\bf B. Denial}\\\\
Man is just  &&     Man is not just\\\\
&{\\Huge\$\\times\$}&\\\\
{\\bf D. Denial} && {\\bf C. Affirmation}\\\\
Man is not not-just && Man is not-just\\\\
\\end{tabular}
\\hfil
\\vspace{1em}

EOF

$pretexts{2}=<<EOF;

\\vspace{1em}
\\hfil
\\begin{tabular}{c c c}
{\\bf A'. Affirmation} && {\\bf B'. Denial}\\\\
Every man is just  &&     Not every man is just\\\\
&{\\Huge\$\\times\$}&\\\\
{\\bf D'. Denial} && {\\bf C'. Affirmation}\\\\
Not every man is not-just && Every man is not-just\\\\
\\end{tabular}
\\hfil
\\vspace{1em}

EOF

$pretexts{3}=<<EOF;

\\vspace{1em}
\\hfil
\\begin{tabular}{c c c}
{\\bf A". Affirmation} && {\\bf B". Denial}\\\\
Not-man is just  &&     Not-man is not just\\\\
&{\\Huge\$\\times\$}&\\\\
{\\bf D". Denial} && {\\bf C". Affirmation}\\\\
Not-man is not not-just && Not-man is not-just\\\\
\\end{tabular}
\\hfil
\\vspace{1em}

EOF

$pretexts{4}=<<EOF;

\\vspace{1em}
\\hfil
\\begin{tabular}{l l}
   It may be.             & It cannot be.\\\\
   It is contingent.      & It is not contingent.\\\\
   It is impossible.      & It is not impossible.\\\\
   It is necessary.       & It is not necessary.\\\\
   It is true.            & It is not true.\\\\
\\end{tabular}
\\hfil
\\vspace{1em}

EOF
$pretexts{5}=<<EOF;

\\vspace{1em}
\\hfil
\\begin{tabular}{p{1.5in} p{1.5in}}
\\hfil{\\bf A.}\\hfil       &      \\hfil{\\bf B.}\\hfil\\\\\\\\
    It may be.                 &  It cannot be.\\\\\\\\
    It is contingent.          &  It is not contingent.\\\\\\\\
  \\rr It is not impossible that it~should be. & \\rr It is impossible that it~should be.\\tn\\tn
  \\rr It is not necessary that it~should be.  &  \\rr It is necessary that it~should not be.\\tn\\tn
\\\\
 \\hfil{\\bf           C. }\\hfil                 &     \\hfil{\\bf  D.}\\hfil\\\\\\\\
   It may not be.             &  It cannot not be.\\\\\\\\
\\rr   It is contingent that \\hspace{2em}it~should not be.   &  \\rr It is not contingent that it~should not be.\\tn\\tn
\\rr   It is not impossible  that it~should not be.      &  \\rr It is impossible that it~should not be.\\tn\\tn
\\rr   It is not necessary that  it~should not be.  &  \\rr It is necessary that it~should be.\\tn\\tn
\\end{tabular}
\\hfil
\\vspace{1em}

EOF


$pretexts{101}=<<EOF;

\\begin{quote}
"Love first of all the Gods she planned."
\\end{quote}

EOF

$pretexts{102}=<<EOF;

\\begin{quote}
    "First of all things was chaos made, and then \\\\
     Broad-breasted earth... \\\\
     And love, `mid all the gods pre-eminent'"
\\end{quote}

EOF

sub startOIndex
{	$volIndexRef=$stub."i.htm";
	open (OINDEX, "> $direc/$volIndexRef");
	print OINDEX <<EOF;
<HTML><HEAD>
<TITLE>$mainTitle</TITLE>
</HEAD>
$body
$up
<CENTER><H1>$mainTitle</H1></CENTER>
<P>
<A NAME="start"></A>
<CENTER>
<TABLE>
<TR><TD WIDTH=40%><I>Volume</I></TD><TD WIDTH=15%><I>Book</I></TD><TD WIDTH=45%><I>Description</I></TD></TR>
EOF
	$volTex=$stub.".tex";
	open (TEXFILE, "> $volTex");
	print TEXFILE <<EOF;
% This is the start of texfile $volTex ($Id)
EOF
};

sub fileStart
{   $csourceTitle=$sourceTitle;
#   chop($csourceTitle);
    print TEXFILE "\n\n\\Avolume\{".$csourceTitle."\}\n\\label{\\thechapter}\n";
};

sub oIndexEntry
{ 	if ($fileType eq "SB") {&oSBIndexEntry};
	if ($fileType eq "MB") {&oMBIndexEntry};
};

sub oSBIndexEntry
{   local($ifile)="$stub$file$book"."i.htm";
    print OINDEX <<EOF;
<TR VALIGN=TOP>
<TD><B>$sourceTitle</B><BR><FONT SIZE=2><B>$sourceTranslator</B><BR>$fileTitle</FONT></TD>
<TD></TD><TD><A HREF="$ifile">$bookTitle</A></TD>
</TR>
EOF
};

sub oMBIndexEntry
{	local($ifile)="$stub$file$book"."i.htm";
        if ($book==1) {$bookDisplay="<TD ROWSPAN=$numBooks><B>$sourceTitle</B><BR><FONT SIZE=2><B>$sourceTranslator</B><BR>$fileTitle</FONT></TD>";}
	else {$bookDisplay=""};
	print OINDEX <<EOF;
<TR VALIGN=TOP>
$bookDisplay
<TD><A HREF="$ifile">$bookSection $book</A></TD>
<TD><FONT SIZE=2>$bookTitle</FONT></TD>
</TR>
EOF
};

sub closeOIndex
{       print OINDEX <<EOF;
</TABLE>
<P>
<HR WIDTH=70%>
$upm$home HTML edition &copy; $rbjsig created $created modified $modified
</CENTER>
</BODY></HTML>
EOF
	close OINDEX;
};

sub nextBookIndex
{	$bookIndexFile="$stub$file$book"."i.htm";
	$bookIndexRef="<A HREF=\"$bookIndexFile\">";
	if ($trace>1) {print "open next book index file: $bookIndexFile\n"};
	open (BOOKINDEX, "> $direc/$bookIndexFile");
	print BOOKINDEX <<EOF;
<HTML><HEAD>
<TITLE>$mainTitle - index for $sourceTitle $bookSection $book - $bookTitle</TITLE>
</HEAD>
$body
<A HREF="$volIndexRef">$upimg</A>
<CENTER><H3>$mainTitle - index for $sourceTitle $bookSection $book</H3>
<H3>$bookTitle</H3>
</CENTER>
<P>
<A NAME="start"></A>
<CENTER>
<TABLE>
<TR><TD><B>Text</B></TD><TD><B>Paragraph Index</B></TD></TR>
EOF
#print "Book Title: $bookTitle\n";
        $cbookTitle=$bookTitle;
	$cbookLetter="";
#        $cbookTitle=~s/\&([^;]*);(.*)/{\$\\$1\$}{$2}/;
	if ($cbookTitle=~/^\s*\&([^;]*);\s*:\s*(.*)$/)
	{$cbookTitle=$2;
	 $cbookLetter="\\Rbj$1"};
         chop($cbookTitle);
#print "cBook Title: $cbookTitle\n";
         print TEXFILE <<EOF;
\n\n\\AM$booktype\{$cbookLetter}{$cbookTitle}
EOF
};

sub bookIndexEntry
{	$partPrefix=$stub.$file.$book.(sprintf("%02d",$part));
	$partIFile=$partPrefix."i.htm";
	$partCFile=$partPrefix."c.htm";
	if ($partTitle eq "") {$partTitle="----"};
	print BOOKINDEX <<EOF;
<TR>
<TD><A HREF="$partCFile">Part $part</A></TD>
<TD><A HREF="$partIFile">$partTitle</A></TD>
</TR>
EOF
        $cpartTitle=$partTitle;
	$cpartTitle=~s/\&([^;]*);/\$\\$1\$/;
	chop($cpartTitle);
    print TEXFILE "\n\n\\Apart{$cpartTitle}\n";
};

sub closeBookIndex
{	print BOOKINDEX <<EOF;
</TABLE>
<P>
<CENTER>
<HR WIDTH=70%>
<A HREF="$volIndexRef">$upimgm</A>$home HTML edition &copy; $rbjsig created $created modified $modified
</CENTER>
</BODY>
</HTML>
EOF
	close BOOKINDEX;
};

sub nextPartIndex
{	open (PARTINDEX, "> $direc/$partIFile");
	print PARTINDEX <<EOF;
<HTML><HEAD>
<TITLE>$mainTitle - index for $sourceTitle $bookSection $book Part $part - $partTitle</TITLE>
</HEAD>
$body
$bookIndexRef$upimg</A>
<A NAME="start"></A>
<CENTER><H3>$mainTitle - index for $sourceTitle $bookSection $book Part $part</H3>
<H3>$partTitle</H3>
<P>
<TABLE>
<TR><TD WIDTH="100">&nbsp;</TD><TD>&nbsp;</TD></TR>
EOF
};

sub partIndexEntry
{	print PARTINDEX <<EOF;
<TR VALIGN=TOP>
<TD><A HREF="$partCFile#$para">Paragraph $para</A></TD>
<TD><!A HREF="$partIFile#start">$paraTitle</A></TD>
</TR>
EOF
};

sub closePartIndex
{	print PARTINDEX <<EOF;
</TABLE>
<P>
<HR WIDTH=70%>
$bookIndexRef$upimgm</A>$home HTML by $rbjsig created $created modified $modified
</CENTER></BODY></HTML>
EOF
	close PARTINDEX;
};

#sub paraindexentry
#{       print CHAPINDEX <<EOF;
#<DT>$parano\. <A HREF="$partFile#$para">$paraTitle</A>
#EOF
#};

sub startPart        
{	open (OUTFILE, "> $direc/$partCFile");
	print OUTFILE <<EOF;
<HTML><HEAD>
<TITLE>$mainTitle $sourceTitle $bookSection $book Part $part $partTitle</TITLE>
</HEAD>
$body
$bookIndexRef$upimg</A>
<A NAME="start"></A>
<CENTER><H3>$mainTitle $sourceTitle $bookSection $book Part $part</H3>
<H2>$partTitle</H2></CENTER>
<P>
EOF
};

sub endPart
{       print OUTFILE <<EOF;
<P><CENTER><HR WIDTH=70%>
$bookIndexRef$upimgm</A>$home HTML edition &copy; $rbjsig created $created modified $modified
</CENTER></BODY></HTML>
EOF
	close OUTFILE;
};

sub startParagraph      
{	if ($trace>4) {print "startParagraph $para\n"};
	if (! (defined $paraTitle)) {$paraTitle =""};
	print OUTFILE <<EOF;
<P>
<A NAME="$para">$para\.</A>
$paraTitle
EOF
	($texline=$paraTitle) =~ s|&|\\&|g;
	    $texline =~ s/\"/{\\dq}/g;
	    $texline =~ s|\'([^\']*)\'|\`$1\'|g;
	    $texline =~ s/(\d+)X(\d+)/$1\$\\times\$$2/g;
	    $texline =~ s/(\d+)X(\d+)/$1\$\\times\$$2/g;
	    $texline =~ s|<\!--pagebreak-->|\\pagebreak|g;
	    $texline =~ s/<gk>([^<]*)<\/gk>/\\textgreek{$1}/g;
#	$texline =~ s|\"([\w\s\.-]*)\"|\`\`$1\'\'|g;
#	$texline =~ s|\'([\w\s\.-]*)\'|\`$1\'|g;
#	$texline =~ s/\"/{\\dq}/g;
#	$texline =~ s/\'/{\\sq}/g;
        print TEXFILE "\n".$texline;
};

sub writeLine2
{	print OUTFILE $_[0];
	($texline=$_[0]) =~ s|&|\\&|g;
	if (not $pre) {
	    if (/<PRE>/) {$texline =~ s|<PRE>|\\begin{verbatim}|; $pre=1}
	    $texline =~ s/(\d+)X(\d+)/$1\$\\times\$$2/g;
	    $texline =~ s/(\d+)X(\d+)/$1\$\\times\$$2/g;
	    $texline =~ s/\"/{\\dq}/g;
	    $texline =~ s|\'([^\']*)\'|\`$1\'|g;
	};
	if ($pre) {
	    if (/<\/PRE>/) {$texline =~ s|</PRE>|\\end{verbatim}|; $pre=0}
	};
#	$texline =~ s|\"([\w\s\.-]*)\"|\`\`$1\'\'|g;
#	$texline =~ s/\'/{\\sq}/g;
	print TEXFILE $texline;
};

# this version of writeline substitutes for the contents of the PRE section

sub writeLine
{	
# translate unicode greek into html entities
    $htmline=$_[0];
    foreach (keys %greek2htm) {
	$key=$_;
	$res=$greek2htm{$key};
	if ($htmline=~/$key/) {
	    print "key: $key; res: $res\n";
	    $htmline =~ s|$key|$res|g;
	    print "line: $htmline\n";
	};
    };
    print OUTFILE $htmline;
# remove <gk></gk> tags
    $htmline=~s/<gk>([^<]*)<\/gk>/$1/g;
# transformations for tex version
    ($texline=$_[0]) =~ s|&|\\&|g;
    if (not $pre) {
	if (/<PRE>/) {
	    $precount+=1;
	    $texline = $pretexts{$precount+($stub eq "m" ? 100 : 0)};
	    $pre=1}
	else {
	    $texline =~ s/<gk>([^<]*)<\/gk>/\\textgreek{$1}/g;
#	    $texline =~ s/<gk>([^<]*)<\/gk>/$1/g;
	    $texline =~ s/(\d+)X(\d+)/$1\$\\times\$$2/g;
	    $texline =~ s/(\d+)X(\d+)/$1\$\\times\$$2/g;
	    $texline =~ s/\"/{\\dq}/g;
#	      $texline =~ s|(katal\'ueis)|\\textgreek\{$1\}|g;
#	      $texline =~ s|(o\>u)|\\textgreek\{$1\}|g;
#	      $texline =~ s|(o\\~\<u)|\\textgreek\{$1\}|g;
	    $texline =~ s|\'([^\']*)\'|\`$1\'|g;
#	      foreach (keys %greek2tex) {
#		  $key=$_;
#		  $res=$greek2tex{$key};
#		  $texline =~ s|$key|$res|g;      
#	      };
	};
	print TEXFILE $texline
    };
    if ($pre) {
	if (/<\/PRE>/) {$pre=0}
    };  
};

$greek2tex{"καταλύεις"}="\\textgreek\{καταλύεις\}";   # lodge
$greek2tex{"μῆνις"}="\\textgreek\{μῆνις\}";         # wrath
$greek2tex{"πήλνξ"}="\\textgreek\{πήλνξ\}";         # helmet
$greek2tex{"οὐλομένην"}="\\textgreek\{οὐλομένην\}";  # destructress
$greek2tex{"οὐλόμενην"}="\\textgreek\{οὐλόμενην\}";  # destructor     
$greek2tex{"οὐ"}="\\textgreek\{οὐ\}";
$greek2tex{"οὗ"}="\\textgreek\{οὗ\}";
#$greek2tex{""}="\\textgreek\{\}";         

$greek2htm{"καταλύεις"}="&#954;&#945;&#964;&#945;&#955;&#973;&#949;&#953;&#962;";
$greek2htm{"μῆνις"}="&#956;&#8134;&#957;&#953;&#962;";
$greek2htm{"πήλνξ"}="&#960;&#942;&#955;&#957;&#958;";
$greek2htm{"οὐλομένην"}="&#959;&#8016;&#955;&#959;&#956;&#941;&#957;&#951;&#957;";
$greek2htm{"οὐλόμενην"}="&#959;&#8016;&#955;&#972;&#956;&#949;&#957;&#951;&#957;";
$greek2htm{"οὐ"}="&#959;&#8016;";
$greek2htm{"οὗ"}="&#959;&#8023;";
#$greek2htm{""}="";

1;
