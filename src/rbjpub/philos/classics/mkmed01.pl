#!/usr/bin/perl -w
# ($Id$)

open(INPUT,"medit.txt");

$dir="descarte/";
$stem="med";
$count=100;
$tail=substr($count,1,2);
$file=$stem.$tail.".htm";

$_ = <INPUT>;
while ($_)
{       &htmfile;
};
close(INPUT);
&med00;

sub htmfile
{       open(OUTPUT,"> $dir$file");
	print STDOUT "output to: $dir$file\n";
	&heading;
	&body;
	close(OUTPUT);
};

sub heading
{       print OUTPUT "<HTML>\n<HEAD><TITLE>";
	while ($_ eq "\n") {$_ = <INPUT>;};
	$title =  "";
	while ($_ ne "\n" && ( ! (/-----/)))
		{s/^\s*//g; chop; s/\s*$//g; print OUTPUT $_." "; 
		$title .= $_." "; $_ = <INPUT>;};
	print OUTPUT "</TITLE>\n</HEAD>\n";
};

sub body
{       	print STDOUT "body count=$count;";
	print OUTPUT <<END;
<BODY BGCOLOR="C0D0D0" TEXT="002020" LINK="002020" VLINK="002020" ALINK="FF0000">
END
	if ($count==100)
	{	print OUTPUT <<END;
<A HREF="../index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=up BORDER=0 ALIGN=LEFT></A>
<A NAME="start"></A>
<CENTER><H2>$title</H2></CENTER>
END
	}
	else
	{       print OUTPUT <<END;
<A HREF="$pfile#end"><IMG SRC="../../../../rbjgifs/left.gif" ALT=left BORDER=0 ALIGN=LEFT></A>
<A HREF="med00.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=up BORDER=0 ALIGN=LEFT></A>
<A NAME="start"></A>
<CENTER><H2>$title</H2></CENTER>
<P>
END
	};
	print STDOUT "count=$count; t1";
	while ($_ && (! /-----/))
	{	if (/^$/)	{print OUTPUT "<P>\n";}
		else	{print OUTPUT;};
		if (eof(INPUT)) {$_ = "";} else {$_ = <INPUT>;};
	};
	print STDOUT " t2";
	print OUTPUT <<END;
<A NAME="end"></A>
<HR>
<CENTER>
END
	if (! ($count==100))
	{	print OUTPUT <<END;
<A HREF="$pfile#end"><IMG SRC="../../../../rbjgifs/left.gif" ALT=left BORDER=0 ALIGN=LEFT></A>
END
	};
	$pfile=$file;
	$tail = substr(++$count,1,2);
	$file=$stem.$tail.".htm";
	if (/-----/)
	{
	print OUTPUT <<END;
<A HREF="$file#start"><IMG SRC="../../../../rbjgifs/right.gif" ALT=right BORDER=0 ALIGN=RIGHT></A>
END
	};
	if ($count==101)
	{	print OUTPUT <<END;
<A HREF="../index.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=up BORDER=0></A>
END
	}
	else
	{	print OUTPUT <<END;
<A HREF="med00.htm"><IMG SRC="../../../../rbjgifs/up.gif" ALT=up BORDER=0></A>
END
	};
	print OUTPUT <<END;
<A HREF="../../../index.htm"><IMG SRC="../../../../rbjgifs/home.gif" ALT=home BORDER=0></A>
&copy; <A HREF="../../../rbj.htm">
<IMG SRC="../../../../rbjgifs/rbjin1.gif" ALT=RBJ ALIGN=absmiddle BORDER=0></A>
created: 2/10/94; modified 24/12/95
<A HREF="000.htm"><IMG SRC="../../../../rbjgifs/c.gif" ALT=c BORDER=0></A>
</CENTER>
</BODY>
END
	if (eof(INPUT)) {$_ = "";} else {$_ = <INPUT>;};
};
	
sub med00
{       	$infile = $stem."00.bak";
	$outfile=$stem."00.htm"; print STDOUT $dir.$outfile;
	rename($dir.$outfile,$dir.$infile) || die "can't rename MED00.HTM\n";
	open (INPUT, $dir.$infile); open(OUTPUT,"> $dir$outfile");
	$_ = <INPUT>;
	while (!/Parts\:\s*and,/) {print OUTPUT; $_ = <INPUT>;};
	$_ =~ s/Parts:  and,/Parts:<BR>\nand,\n<DL> /;
	foreach $count (101..106)
	{       while (!/in\s*the/) {print OUTPUT; $_ = <INPUT>;};
		$pointer = $stem.(substr($count,1)).".htm#start";
		$_ =~ s/(in\s*the\s*\w*),/\n<DT><A HREF="$pointer">$1<\/A>,\n<DD>/;
		print OUTPUT; $_ = <INPUT>;
	};
	while (!/<P>/) {print OUTPUT; $_ = <INPUT>;};
	$_ =~ s/<P>/<\/DL>\n$&/; print OUTPUT;
	while (<INPUT>) {print OUTPUT;}; close(STDIN); close(STDOUT);
};




