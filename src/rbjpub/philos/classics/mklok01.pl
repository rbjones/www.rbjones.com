#!/usr/bin/perl -w
# ($Id$)
$modified="2015-06-14";
$rbjgifs="../../../../rbjgifs";
$rbjhref="<A HREF=\"http://www.rbjones.com/rbjpub/rbj.htm\">";
$rbjimg="<IMG SRC=\"$rbjgifs/rbjin1.gif\" ALT=RBJ ALIGN=TOP BORDER=0>";
$homeimg="<IMG SRC=\"$rbjgifs/home.gif\" ALT=HOME BORDER=0>";
$upimg="<IMG SRC=\"$rbjgifs/up.gif\" ALT=UP BORDER=0 ALIGN=LEFT>";
$rbjsig="$rbjhref$rbjimg</A>";
$homeref="<A HREF=\"../../../index.htm\">";
$upref="<A HREF=\"../index.htm\">";
$home="$homeref$homeimg</A>";
$up="$upref$upimg</A>";
$body="<BODY BGCOLOR=\"#bbeeee\">";
$direc="locke";
print "firstpass\n";

&firstpass;

sub paraindexentry
{       print CHAPINDEX <<EOF;
<DT>$parano\. <A HREF="$chapfile#$parano">$paratitle</A>
EOF
};

sub chapterindexentry
{       print BOOKINDEX <<EOF;
<DT><A HREF="$file#start">$chapter</A>
<DD><A HREF="$chapifile#start">$chaptitle</A>
EOF
};

sub bookindexentry
{       local($file);
	$file=$stem.(substr(++$bookno,1,1)).".htm";
	$chapno=100;
	print VOLINDEX <<EOF;
<DT><A HREF="$file">$book</A>
<DD>$booktitle
EOF
};

sub closechapindex
{       print CHAPINDEX <<EOF;
</DL>
<P>
<HR>
<CENTER>
$bookindexref$upimg</A> HTML by $rbjsig created 1994/10/29 modified $modified
</CENTER></BODY></HTML>
EOF
	close CHAPINDEX;
};

sub closebookindex
{       print BOOKINDEX <<EOF;
</DL>
<P>
<HR>
<CENTER>
$volindexref$upimg</A> HTML by $rbjsig created 94/10/29; modified $modified
</CENTER>
</BODY></HTML>
EOF
	close BOOKINDEX;
};

sub closevolindex
{       print VOLINDEX <<EOF;
</DL>
<P>
<HR>
<CENTER>
$up$home HTML by $rbjsig created 94/10/29; modified $modified
</CENTER>
</BODY></HTML>
EOF
	close VOLINDEX;
};

sub nextchapindex
{       $chapsuff=(substr($bookno,1,1))."c".(substr(++$chapno,1,2)).".htm";
      $chapifile="cib".$chapsuff;
	print "next chapter index file = $chapifile\n";
	open (CHAPINDEX, "> $direc/$chapifile");
	print CHAPINDEX <<EOF;
<HTML><HEAD><TITLE>
Locke - ECHU - index for $book $chapter $chaptitle
</TITLE></HEAD>
$body
$bookindexref$upimg</A>
<A NAME="start"></A>
<CENTER><H1>Index for $chapter</H1><H1>$chaptitle</H1></CENTER>
<P>
<DL>
EOF
	print "INDEX for $chapter in $chapifile\n";
};

sub nextbookindex
{     local($file);
	$file=$stem.(substr($bookno,1,1)).".htm";
	print "next book index file = $file\n";
	open (BOOKINDEX, "> $direc/$file");
	$bookindexref="<A HREF=\"$file\">";
	print BOOKINDEX <<EOF;
<HTML><HEAD><TITLE>
Locke - ECHU - index for $book $booktitle
</TITLE></HEAD>
$body
$volindexref$upimg</A>
<CENTER><H1>Index for $book</H1><H1>$booktitle</H1></CENTER>
<P>
<A NAME="start"></A>
<DL>
EOF
	print "INDEX for $book in $file\n";
};

sub nextchapfile
{     $tail=substr(++$count,1,4);
	$file="ctb".$chapsuff;
#	$file=$stem.$tail.".htm";
#	$ochapfile=$chapfile;
	$chapfile=$file;
	open (OUTFILE, "> $direc/$file");
	print "$book $chapter $file\n";
};

sub endchap
{       print OUTFILE <<EOF;
<P><HR><CENTER>
$bookindexref$upimg</A> HTML by $rbjsig created 94/10/29; modified $modified
</CENTER></BODY></HTML>
EOF
	close OUTFILE;
};

sub strip
{       $_[0] =~ s/^\s*\b(.*)\b\s*$/$1/; $_[0];
};

sub parano
{       if (s/(^\s*)(\d*)(\.)(.*)$/$1$4/) {$2} else {""};
};

sub paratitle
{       local($paratitle);
	$paratitle="";
	while (/^([^.\?:;]*)$/) {$parat=$1; chop $parat; $paratitle.=" "; $paratitle.=$parat; $_=<INPUT>;};
	if (s/^([^.\?:;]*[.\?:;]\s*)(.*)$/$2/) {$parat=$1; chop $parat; $paratitle.=" "; $paratitle.=$parat;};
	chop;
	while ((/^\s*$/)) {$_=<INPUT>; chop;};
	$paratitle;
};

sub title
{     local($title);
	$_ = <INPUT>; $title="";
	until (/^\s*$/) {$title.=&strip($_); $_ = <INPUT>;};
	$title;
};

sub firstpass
{     open(INPUT,"locke.txt");
#	$_ = <STDIN>;
	$_ = <INPUT>;
	$book="Book 0"; $chapter="Chapter 0";
	$bookno=10;
	$chapno=100;
	$parano=0;
	print "$direc\n";        
	$stem="lok";
	$count=10004;
	$tail=substr($count,1,4);
	$file=$stem.$tail.".htm";
	print "output file: $direc/$file\n";
	open(VOLINDEX,"> $direc/index.htm");
	$volindexref="<A HREF=\"index.htm\">";
	print VOLINDEX <<EOF;
<HTML><HEAD><TITLE>
Locke - An Essay Concerning Human Understanding
</TITLE></HEAD>
$body
$up
<CENTER><H1>An Essay Concerning Human Understanding</H1></CENTER>
<P>
<A NAME="start"></A>
<DL>
<DT><A HREF="ctb0prea.htm">Preamble</A>
<DT><A HREF="ctb0epis.htm">Epistle</A>
<DT><A HREF="ctb0intr.htm">Introduction</A>
EOF
	&preamble;
	&epistle;
	&introduction;
	&books;
	&closevolindex;
};

sub preamble
{       print "preamble\n";
	$chapsuff="0prea.htm";
	&nextchapfile;
	print OUTFILE <<EOF;
<HTML><HEAD><TITLE>
LOCKE - AN ESSAY CONCERNING HUMAN UNDERSTANDING
</TITLE></HEAD>
$body
$volindexref$upimg</A>
<A NAME="start"> </A>
<CENTER>
<H2>1690</H2>
<H1>AN ESSAY CONCERNING HUMAN UNDERSTANDING<BR>
by John Locke
</H1>
<H5>
TO THE RIGHT HONOURABLE LORD THOMAS, EARL OF PEMBROKE AND MONTGOMERY,
BARRON HERBERT OF CARDIFF, LORD ROSS, OF KENDAL, PAR, FITZHUGH, MARMION,
ST. QUINTIN, AND SHURLAND;
LORD PRESIDENT OF HIS MAJESTY'S MOST HONOURABLE PRIVY COUNCIL;
AND LORD LIEUTENANT OF THE COUNTY OF WILTS, AND OF SOUTH WALES.
</H5>
</CENTER>
<H2>MY LORD</H2>
EOF
	until (/MY LORD/ || !($_)) {$_ = <INPUT>;};
	$_ = <INPUT>;
	until (/EPISTLE/)
		{if (/^ /) {print OUTFILE "<P>\n";};
		print OUTFILE; $_ = <INPUT>;};
	$bookindexref=$volindexref;
	&endchap;
};

sub epistle
{       print "epistle\n";
	$chapsuff="0epis.htm";
	&nextchapfile;
	print OUTFILE <<EOF;
<HTML><HEAD><TITLE>
LOCKE - ECHU - EPISTLE TO THE READER
</TITLE></HEAD>
$body
$volindexref$upimg</A>
<A NAME="start"></A>
<CENTER><H1>
EOF
	until (/I HAVE/) {print OUTFILE "$_<BR>\n"; $_ = <INPUT>;};
	print OUTFILE "</H1></CENTER>\n<P>\n$_";
	$_ = <INPUT>;
	until (/INTRODUCTION/)
		{if (/^ /) {print OUTFILE "<P>\n";};
		print OUTFILE; $_=<INPUT>;};
	$bookindexref=$volindexref;
	&endchap;
};

sub introduction
{       print "introduction\n";       
	$chapsuff="0intr.htm";
	&nextchapfile;
	print OUTFILE <<EOF;
<HTML><HEAD><TITLE>
LOCKE - ECHU - INTRODUCTION
</TITLE></HEAD>
$body
$volindexref$upimg</A>
<CENTER><H1>INTRODUCTION</H1>
<H3>
EOF
	until(/INTRODUCTION/) {$_ = <INPUT>;};
	$_ = <INPUT>;
	until (/As thou/) {print OUTFILE; $_ = <INPUT>;};
	print OUTFILE "</H3></CENTER>\n<P>\n";
	until (/INTRODUCTION/) {if (/^ /) {print OUTFILE "<P>\n";}; 
			print OUTFILE; $_ = <INPUT>;};
	print OUTFILE "<CENTER><H2>INTRODUCTION</H2></CENTER>\n";
	$_ = <INPUT>;
	until (/^\s*BOOK/) {if (/^ /) {print OUTFILE "<P>\n";}; 
			print OUTFILE; $_ = <INPUT>;};
	print "end of introduction: $_\n";
	$bookindexref=$volindexref;
	&endchap;
};

sub books
{       print "start of books: $_\n";
	while (/BOOK/) {&book;};
};
	
sub book
{     $book=&strip($_);
	$booktitle=&title; $_=<INPUT>;
	&bookindexentry;
	&nextbookindex;
	while (/Chapter/) {&chapter;};
	&closebookindex;
};
	
sub chapter        
{	$chapter=&strip($_);
	print "$chapter\n";
	$chaptitle=&title; $_=<INPUT>;
	&nextchapindex;
	&nextchapfile;
	while (/^\s*$/) {$_=<INPUT>;};
	&chapterindexentry;
	print OUTFILE <<EOF;
<HTML><HEAD><TITLE>
Locke ECHU $book $chapter $chaptitle
</TITLE></HEAD>
$body
$bookindexref$upimg</A>
<A NAME="start"></A>
<CENTER><H1>$chapter</H1><P>
<H1>$chaptitle</H1></CENTER>
<P>
EOF
	until (/^\s*BOOK/ || /^\s*Chapter/ || !($_))
		{&paragraph;};
	&endchap;
	&closechapindex;
};

sub paragraph      
{#       &nextparafile;
	$parano=&parano;
	$paratitle=&paratitle;
	print "Paragraph $parano $paratitle\n";
	&paraindexentry;
	print OUTFILE <<EOF;
<P>
<A NAME="$parano">
$parano\.</A> <EM>$paratitle</EM>
EOF
#       print POUTFILE <<EOF;
#<HTML><HEAD><TITLE>
#Locke ECHU $book $chapter $paratitle
#</TITLE></HEAD>
#$body
#<A NAME="start"></A>
#<H1>$chapter</H1><P>
#<H2>$chaptitle</H2><P>
#<H3>$parano\. $paratitle</H3><P>
#EOF
	until (/^\s*BOOK/ || /^\s*Chapter/ || (/^\s+\d+\..*$/) || !($_))
		{if (/^\s/) {print OUTFILE "<P>\n";
#                       print POUTFILE "<P>\n";
			}; 
		print OUTFILE;
#               print POUTFILE;
		if (eof(INPUT)) {$_="";} else {$_ = <INPUT>;};
		};
#       &endpara;
};
