#!/usr/bin/perl -w
# ($Id)
#use strict;
use warnings;
open(INPUT,"<","berkeley.txt") || die "failed to open file berkeley.txt\n";
my $modified="96/11/18";
#$stem="brk";
#$count=0;
#$tail=sprintf("2.2x",$count);
#$file=$stem.$tail.".htm";
my $direc="berkeley";
$/="\r";

&preamble;
&preface;
&introduction;
&treatise;
&contents;

close(INPUT);

sub strip
{       $_[0] =~ s/^\s*\b(.*)\b\s*$/$1/; $_[0];
};

sub preamble
{       open(OUTPUT,"> $direc/brkpream.htm");
	$_ = <INPUT>; my $year = &strip($_);
	$_ = <INPUT>; my $title = &strip($_);
#	$_ = <STDIN>;
	$_ = <INPUT>; my $author = &strip($_);
	print OUTPUT <<EOF;
<HTML>
<HEAD>
<TITLE>$title</TITLE>
</HEAD>
<BODY BGCOLOR="#e0e0f0">
<A NAME="start"></A>
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" BORDER=0 ALT="up" ALIGN=LEFT></A>
<CENTER><H2>$year</H2>
<P>
<H1>$title</H1>
<P>
<H2>$author</H2>
<P>
EOF
	$_ = <INPUT>;
	print OUTPUT "<H5>";
	until (/MY LORD/)
	{       print OUTPUT ((&strip($_))."\n");
		$_ = <INPUT>;
	};
	print OUTPUT "</H5>\n<H4>MY LORD</H4></CENTER>\n";
	$_ = <INPUT>;
	while (!/MY LORD/)
	{       if (/^ (.*$)/) {print OUTPUT "<P>\n";}; print OUTPUT;
		$_ = <INPUT>;
	};
	print OUTPUT "\n<CENTER><B>\n";
	while (!/PREFACE/)
	{       if (/^ (.*$)/) {print OUTPUT "<P>\n";}; print OUTPUT;
		$_ = <INPUT>;
	};
	print OUTPUT <<EOF;
</B></CENTER>
<P>
<A NAME="end"></A>
<HR WIDTH=70%>
<CENTER>
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=UP BORDER=0></A><A HREF="../../../index.htm"><IMG SRC="../../../../rbjgifs/home.gif" ALT=HOME BORDER=0></A> this HTML edition &copy; <A HREF="http://www.rbjones.com/rbjpub/rbj.htm"><IMG SRC="../../../../rbjgifs/rbjin1.gif" ALT=RBJ ALIGN=MIDDLE BORDER=0></A> created 1994; modified $modified
<A HREF=\"brkpref.htm#start\"><IMG SRC="../../../../rbjgifs/right.gif" ALT="right" BORDER=0 ALIGN=MIDDLE></A>
</CENTER>
</BODY>
EOF
	close(OUTPUT);
};

sub preface
{       open(OUTPUT,"> $direc/brkpref.htm");
	print OUTPUT <<EOF;
<HTML>
<HEAD>
<TITLE>PREFACE</TITLE>
</HEAD>
<BODY BGCOLOR="#e0e0f0">
<A NAME="start"></A>
<A HREF="brkpream.htm#end"><IMG SRC="../../../../rbjgifs/left.gif" BORDER=0 ALT="left" ALIGN=LEFT></A>
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" BORDER=0 ALT="up"></A>
<CENTER>
<H1>PREFACE</H1>
</CENTER>
<P>
EOF
	$_ = <INPUT>;
	while (/PREFACE/) {$_ = <INPUT>;};
	while (!/INTRODUCTION/)
	{       if (/^ (.*$)/) {print OUTPUT "<P>\n";}; print OUTPUT;
		$_ = <INPUT>;
	};
	print OUTPUT <<EOF;
<P>
<A NAME="end"></A>
<P>
<HR WIDTH=70%>
<CENTER>
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=UP BORDER=0></A><A HREF="../../../index.htm"><IMG SRC="../../../../rbjgifs/home.gif" ALT=HOME BORDER=0></A> this HTML edition &copy; <A HREF="http://www.rbjones.com/rbjpub/rbj.htm"><IMG SRC="../../../../rbjgifs/rbjin1.gif" ALT=RBJ ALIGN=MIDDLE BORDER=0></A> created 1994; modified $modified
<A HREF="brkintro.htm#start"><IMG SRC="../../../../rbjgifs/right.gif" ALT="right" BORDER=0 ALIGN=MIDDLE></A>
</CENTER>
</BODY>
EOF
	close(OUTPUT);
};

sub introduction
{       open(OUTPUT,"> $direc/brkintro.htm");
	print OUTPUT <<EOF;
<HTML>
<HEAD>
<TITLE>INTRODUCTION</TITLE>
</HEAD>
<BODY BGCOLOR="#e0e0f0">
<A NAME="start"></A>
<A HREF="brkpref.htm#end"><IMG SRC="../../../../rbjgifs/left.gif" BORDER=0 ALT="left" ALIGN=LEFT></A>
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" BORDER=0 ALT="up" ALIGN=LEFT></A>
<CENTER><H1>INTRODUCTION</H1></CENTER>
<P>
EOF
	$_ = <INPUT>;
	while (/INTRODUCTION/) {$_ = <INPUT>;};
	while (!/TREATISE/)
	{       if (/^ (.*$)/) {print OUTPUT "<P>\n";}; print OUTPUT;
		$_ = <INPUT>;
	};
	print OUTPUT <<EOF;
<P>
<A NAME="end"></A>
<P>
<HR WIDTH=70%>
<CENTER>
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=UP BORDER=0></A><A HREF="../../../index.htm"><IMG SRC="../../../../rbjgifs/home.gif" ALT=HOME BORDER=0></A> this HTML edition &copy; <A HREF="http://www.rbjones.com/rbjpub/rbj.htm"><IMG SRC="../../../../rbjgifs/rbjin1.gif" ALT=RBJ ALIGN=MIDDLE BORDER=0></A> created 1994; modified $modified
<A HREF="brktreat.htm#start"><IMG SRC="../../../../rbjgifs/right.gif" ALT="right" BORDER=0 ALIGN=MIDDLE></A>
</CENTER>
</BODY>
EOF
	close(OUTPUT);
};

sub treatise
{       open(OUTPUT,"> $direc/brktreat.htm");
	print OUTPUT <<EOF;
<HTML>
<HEAD>
<TITLE>TREATISE</TITLE>
</HEAD>
<BODY BGCOLOR="#e0e0f0">
<A NAME="start"></A>
<A HREF="brkintro.htm#end"><IMG SRC="../../../../rbjgifs/left.gif" BORDER=0 ALT="left" ALIGN=LEFT></A>
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" BORDER=0 ALT="up" ALIGN=LEFT></A>
<CENTER>
<H1>TREATISE</H1>
<H2>CONCERNING THE PRICIPLES OF HUMAN KNOWLEDGE</H2>
</CENTER>
<P>
EOF
	$_ = <INPUT>;
	while (!/1./) {$_ = <INPUT>;};
	while ($_)
	{       if (/^ (.*$)/) {print OUTPUT "<P>\n";}; print OUTPUT;
		$_ = <INPUT>;
	};
	print OUTPUT <<EOF;
<P>
<A NAME="end"></A>
<HR WIDTH=70%>
<CENTER>
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=UP BORDER=0></A><A HREF="../../../index.htm"><IMG SRC="../../../../rbjgifs/home.gif" ALT=HOME BORDER=0></A> this HTML edition &copy; <A HREF="http://www.rbjones.com/rbjpub/rbj.htm"><IMG SRC="../../../../rbjgifs/rbjin1.gif" ALT=RBJ ALIGN=MIDDLE BORDER=0></A> created 1994; modified $modified
</CENTER>
</BODY>
EOF
	close(OUTPUT);
};

sub contents
{       open(OUTPUT,"> $direc/index.htm");
	print OUTPUT <<EOF;
<HTML>
<HEAD>
<TITLE>TREATISE</TITLE>
</HEAD>
<BODY BGCOLOR="#e0e0f0">
<A NAME="start"></A>
<A HREF="../index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=UP BORDER=0 ALIGN=LEFT></A>
<CENTER><H1>A TREATISE CONCERNING the PRINCIPLES of HUMAN KNOWLEDGE</H1>
<P>
by George Berkeley
<P>
<TABLE><TR><TD>
<UL>
<LI><A HREF="brkpream.htm">Preamble</A>
<LI><A HREF="brkpref.htm">Preface</A>
<LI><A HREF="brkintro.htm">Introduction</A>
<LI><A HREF="brktreat.htm">Treatise</A>
</UL>
</TD></TR></TABLE>
</CENTER>
<P>
<HR WIDTH=70%>
<CENTER>
<A HREF="../index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=UP BORDER=0></A><A HREF="../../../index.htm"><IMG SRC="../../../../rbjgifs/home.gif" ALT=HOME BORDER=0></A> this HTML edition &copy; <A HREF="http://www.rbjones.com/rbjpub/rbj.htm"><IMG SRC="../../../../rbjgifs/rbjin1.gif" ALT=RBJ ALIGN=MIDDLE BORDER=0></A> created 1994; modified $modified
</CENTER>
</BODY>
</HTML>
EOF
	close(OUTPUT);
};

