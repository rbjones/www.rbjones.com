#!/usr/bin/perl -w
# ($Id$)

require "linkmon1.pl";

open(INPUT,"monad.txt") || die "can't open monad.txt";

#$stem="brk";
#$count=0;
#$tail=sprintf("2.2x",$count);
#$file=$stem.$tail.".htm";

&preamble;
#&preface;
#&introduction;
#&treatise;
#&contents;

close(INPUT);

sub strip
{       $_[0] =~ s/^\s*\b(.*)\b\s*$/ $1 /; $_[0];
};

sub preamble
{       open(OUTPUT,"> leibniz/monad.htm");
	$_ = <INPUT>; 
	$_ = <INPUT>; $title = &strip($_);
	$_ = <INPUT>; $author = &strip($_);
	$_ = <INPUT>; $transl = &strip($_);
	print OUTPUT <<EOF;
<HTML>
<HEAD>
<LINK REL=STYLESHEET TYPE="text/css" HREF="../../../prof/p1sty.txt" TITLE="Content">
<TITLE>$title</TITLE>
</HEAD>
<BODY CLASS=co2>
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=up BORDER=0 ALIGN=LEFT></A>
<A HREF="monglos.htm"><IMG SRC="../../../../rbjgifs/gloss.gif" ALT=up Border=0 ALIGN=RIGHT></A>
<A NAME="start"></A>
<CENTER>
<H1>$title</H1>
<P>
<H2>$author</H2>
<P>
<H3>$transl</H3>
</CENTER>
<P>
EOF
	$_ = <INPUT>;
	while (!/THE END/)
	{	&link;
		if (/^ (.*$)/) {print OUTPUT "<P>\n";};
		if (/^\s*(\d+)\./) {print OUTPUT "<A NAME=\"$1\"><\/A>\n";};
		print OUTPUT;
		$_ = <INPUT>;
	};
	print OUTPUT <<EOF;
<P>
<A NAME="end"></A>
<H2>THE END</H2>
<P>
<HR>
<CENTER>
<A HREF="index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=up BORDER=0></A>
<A HREF="../../../index.htm"><IMG SRC="../../../../rbjgifs/home.gif" ALT=home BORDER=0></A>
&copy; <A HREF="../../../rbj.htm">
<IMG SRC="../../../../rbjgifs/rbjin1.gif" ALT=RBJ ALIGN=absmiddle BORDER=0></A>
created: 1994/12/4; modified 1999/1/30
</CENTER>
</BODY>
EOF
	close(OUTPUT);
};





