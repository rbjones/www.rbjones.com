$modified="2009/04/26";
$created="1996/11/24";

# The following kinds of files are created by the subroutines below:
# (1) Overall index with one entry per file or book (some files are
# 	a single book, some multiple books).
# (2) Part indexes for each book
# (3) Paragraph indexes for each Part
# (4) Part files containing the text of the work

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

sub startOIndex
{	$volIndexRef=$stub."i.htm";
	open (OINDEX, "> $direc/$volIndexRef");
	print OINDEX <<EOF;
<HTML><HEAD><TITLE>
$mainTitle
</TITLE></HEAD>
$body
$up
<CENTER><H1>$mainTitle</H1></CENTER>
<P>
<A NAME="start"></A>
<CENTER>
<TABLE>
<TR><TD WIDTH=40%><I>Volume</I></TD><TD WIDTH=15%><I>Book</I></TD><TD WIDTH=45%><I>Description</I></TD></TR>
EOF
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
<TD><A HREF="$ifile">Book $book</A></TD>
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
<HTML><HEAD><TITLE>
$mainTitle - index for $sourceTitle Book $book
</TITLE></HEAD>
$body
<A HREF="$volIndexRef">$upimg</A>
<CENTER><H3>$mainTitle - index for $sourceTitle Book $book</H2></CENTER>
<P>
<A NAME="start"></A>
<CENTER>
<TABLE>
<TR><TD><B>Text</B></TD><TD><B>Paragraph Index</B></TD></TR>
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
<HTML><HEAD><TITLE>
$mainTitle - index for $sourceTitle Book $book Part $part - $partTitle
</TITLE></HEAD>
$body
$bookIndexRef$upimg</A>
<A NAME="start"></A>
<CENTER><H3>$mainTitle - index for $sourceTitle Book $book Part $part</H3><H2>$partTitle</H2>
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
$bookIndexRef$upimgm</A>$home HTML by $rbjsig created 94/10/29 modified $modified
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
<HTML><HEAD><TITLE>
$mainTitle $sourceTitle Book $book Part $part $partTitle
</TITLE></HEAD>
$body
$bookIndexRef$upimg</A>
<A NAME="start"></A>
<CENTER><H3>$mainTitle $sourceTitle Book $book Part $part</H3>
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
};

sub writeLine
{	print OUTFILE $_[0];
};

1;