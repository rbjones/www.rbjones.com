#!/usr/bin/perl -w
# ($Id)

# Kant's Critique of Pure Reason has a more complex section structure 
# than works I have previously converted.
# The following hierarchic divisions are present:
#       1       Volume (my term)
#       2       Part
#       3       Division
#       4       Book
#       5       Chapter
#       6       Section
#       7       Subsection (my term)
# Not all of these layers are present throughout, and introductions
# are generally a law unto themselves.
# The policy I have adopted for dividing the work into files is to divide 
# at the smallest unit greater than a paragraph.
# Indexes are generated broken into files at each level, and also as a
# single file with nested lists of pointers.

$initial="1994/12/23";
#$created="1997/4/14";
$modified="1999/8/29";
#$author="kant";
$kanttext=$ARGV[0];
$kantstru=$ARGV[1];
$destdir=$ARGV[2];
$body="<BODY CLASS=co3>";

print "destdir $destdir\n";

&work;

sub strip
{       $_[0] =~ s/^\s*\b(.*)\b\s*$/$1/; $_[0];
};

sub parano
{       s/(^\s*)(\d*)(\.)(.*)$/$1$4/;
	$2;
};

sub paratitle
{       local($paratitle);
	$paratitle="";
	while (/^([^.\?]*)$/) {chop $1; $paratitle.=$1; $_=<INPUT>;};
	if (s/^([^.\?]*[.\?]\s*)(.*)$/$2/) {chop $1; $paratitle.=$1;};
	chop;
	while ((/^\s*$/)) {$_=<INPUT>; chop;};
	$paratitle;
};

sub title
{       local($title);
	$_ = <INPUT>; $title="";
	until (/^\s*$/) {$title.=&strip($_); $_ = <INPUT>;};
	$title;
};

sub work
{       open(INPUT,$kanttext) || die "failed to open $kanttext\n";
	$_ = <INPUT>;
	$stem="kant";
	$count=1000;
	open(STRUCT,$kantstru) || die "failed to open $kantstru\n";
	$_=<STRUCT>;
	$oldlevel=0; $level=0;
	if (/^([^\s]*)\s*([^\s]*)\s*([^\s]*)\s*([^\s]*)\s*(\d*)\s*([^!]*)!(.*)$/)
		{$nextsubindex=$1; $nextcontent=$2;
		$nextsection=$3; $nextlevel=$4; $nextskip=$5;
		$shorttitle=$6; $nexttitle=$6.$7;
#		print "content $nextcontent; subindex $nextsubindex; section $nextsection; level: $nextlevel; skip: $nextskip; title: $nexttitle\n";
		};
	open(INDEX,"> $destdir/indexl.htm");
	print INDEX <<EOF;
<HTML><HEAD>
<LINK REL=STYLESHEET TYPE="text/css" HREF="../../../prof/p1sty.txt" TITLE="Factasia">
<TITLE>Kant - CPUR - contents</TITLE>
<META name="description" contents="Emmanual Kant's Critique of Pure Reason - contents listing">
<META name="keywords" contents="RbJ FactasiA PhilosophY KanT">
</HEAD>
$body
<A HREF="../index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT="Up" BORDER=0 ALIGN=LEFT WIDTH=22 HEIGHT=12></A>
<BR CLEAR=ALL>
<CENTER>
<H2>Emmanual Kant</H2>
<H1>Critique of Pure Reason</H1>
<H2>translated by Meiklejohn</H2>
<H3>Contents (single-level)</H3>
<H4><A HREF="index.htm">two-level contents</A></H4>
</CENTER>
<P>
<A NAME="start"></A>
<DL>
EOF
	while (!eof(STRUCT))
	{&struct;
	};
print INDEX <<EOF;
</DL>
<P>
<CENTER>
<HR WIDTH="70%">
converted to HTML for <A HREF="http://www.rbjones.com/">RBJones.com</A> by <A HREF="../../../rbj.htm"><IMG SRC="../../../../rbjgifs/rbjin1.gif" ALT="RBJ" BORDER=0 ALIGN=ABSMIDDLE WIDTH=44 HEIGHT=19></A><BR>
first edition $initial last modified $modified
</CENTER>
</BODY>
</HTML>
EOF
	close INDEX; close OUTPUT; close STRUCT; close INPUT;
};

sub struct
{	$content=$nextcontent;
#   $subindex=$nextsubindex;
#	$section=$nextsection;
	$oldlevel=$level; $level=$nextlevel;
#	$skip=$nextskip; 
	$title=$nexttitle; 
	if ($content)
	{	$tail=substr($count++,1,4);
		$file=$stem.$tail.".htm";
	};
	$_=<STRUCT>;
	if (/^([^\s]*)\s*([^\s]*)\s*([^\s]*)\s*([^\s]*)\s*(\d*)\s*([^!]*)[!]*(.*)$/)
		{$nextsubindex=$1; $nextcontent=$2;
		$nextsection=$3; $nextlevel=$4; $nextskip=$5;
		$shorttitle=$6; $nexttitle=$6.$7;
#		print "content $nextcontent; subindex $nextsubindex; section $nextsection; level: $nextlevel; skip: $nextskip; title: $nexttitle\n";
		};
	if ($level<$oldlevel) {&uplevels;};
	if ($level>$oldlevel) {&downlevels;};
	&samelevel;
};

sub samelevel
{       if ($content)
	{
#	    print "output file: $destdir/$file\n";
		print INDEX "<DT><A HREF=\"$file\">$title</A>\n";
		open(OUTPUT,"> $destdir/$file");
		print OUTPUT <<EOF;
<HTML><HEAD>
<LINK REL=STYLESHEET TYPE="text/css" HREF="../../../prof/p1sty.txt" TITLE="Factasia">
<TITLE>$title</TITLE>
<META name="description" contents="Emmanual Kant's Critique of Pure Reason - $title">
<META name="keywords" contents="RbJ FactasiA PhilosophY KanT">
</HEAD>
$body
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT="Up" BORDER=0 ALIGN=LEFT WIDTH=22 HEIGHT=12></A>
<BR CLEAR=ALL>
<CENTER><H1>$title</H1></CENTER>
<P>
<A NAME="start"></A>
EOF
		$finished=0;
		while (!(eof(INPUT)||$finished))
			{$_ = <INPUT>;
			if (/$shorttitle/)
				{$finished = 1; while ($nextskip--) {$_=<INPUT>;};}
			else	{if (/^\s/) {print OUTPUT "<P>\n";}; print OUTPUT;};
			};
		print OUTPUT <<EOF;
<CENTER>
<HR WIDTH="70%">
converted to HTML for <A HREF="http://www.rbjones.com/">RBJones.com</A> by <A HREF="../../../rbj.htm"><IMG SRC="../../../../rbjgifs/rbjin1.gif" ALT="RBJ" BORDER=0 ALIGN=ABSMIDDLE WIDTH=44 HEIGHT=19></A><BR>
first edition $initial last modified $modified
</CENTER>
</BODY>
</HTML>
EOF
		close OUTPUT;
	}
	else
	{	print INDEX "<DT><DD>$title\n";
		$finished=0;
		while (!(eof(INPUT)||$finished))
			{$_ = <INPUT>;
			if (/$shorttitle/)
				{$finished = 1; while ($nextskip--) {$_=<INPUT>;};}
			};
	};
};

sub uplevels
{       for ($l = $oldlevel; $l > $level; $l--) {print INDEX "</DL>\n";};
};

sub downlevels
{       for ($l = $oldlevel; $l < $level; $l++) {print INDEX "<DL>\n";};
};

