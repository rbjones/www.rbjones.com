# $Id: testconv.pl,v 1.1 2010/02/06 16:21:37 rbj Exp $
require "trans1.pl";
$created="95/7/5";
$updated="96/7/8";
$file=$ARGV[0];
# heading level for plain NH
$HB=2;
# flag for <PRE> sections
$pre=0;
if (-r "$file.TXT"){open (INPUT, "$file.TXT");}
else {die "File $file.TXT not readable\n";};
#if (-e "$file.HTM"){die "File $file.HTM already exists\n";}
#else {open (OUTPUT, "> $file.HTM");};
open (OUTPUT, "> $file.HTM");

$_=<INPUT>;
while ($_)
{&nextstructure;};
&windup;
exit;
print "PS = $PS; VS= $VS\n";

sub nextline
{if (eof(INPUT)) {$_="";} else {$_=<INPUT>; &translate;};};

sub proctocom
{&nextline;
while ($_ && !(/^$_[0]/)) {&nextstructure;};
};

sub copytodot
{&nextline;
while ($_ && !(/^\./)) {print OUTPUT; &nextline;};
};

sub nextstructure
{
if      (/^\.nr PS (\d+)/) {$PS=$1;}
elsif   (/^\.nr VS (\d+)/) {$VS=$1;}
elsif   (/^\.TL/){$TL = <INPUT>; chop($TL);
                print OUTPUT "<HTML><HEAD><TITLE>$TL</TITLE></HEAD>\n";}
elsif   (/^\.AU/){&doAU;}
elsif   (/^\.AI/){$AI = <INPUT>; chop($AI);
                print OUTPUT "<CENTER><H4>$AI</H4></CENTER>\n";}
elsif   (/^\.AB/){print OUTPUT "<CENTER><H3>Abstract</H3>\n";
                &copytodot;
                print OUTPUT "</CENTER>\n<P>\n";}
elsif   (/^\.NH (\d*)/){$NH = $1; $HL=$HB+$NH-1; $HDNG=<INPUT>;
                chop($HDNG);
                print OUTPUT "<CENTER><H$HL>$HDNG</H$HL></CENTER>\n";}
elsif   (/^\.NH/){$HDNG=<INPUT>; chop($HDNG);
                print OUTPUT "<CENTER><H$HB>$HDNG</H$HB></CENTER>\n";}
elsif   (/^\.LP/){print OUTPUT "<P>\n";}
elsif   (/^\.RS/){&doRS;}
elsif   (/^\.DS/){print OUTPUT "<PRE>\n";}
elsif   (/^\.DE/){print OUTPUT "<\/PRE>\n";}
elsif   (/^\.sv/){print OUTPUT "<PRE>\n";}
elsif   (/^\.sw/){print OUTPUT "<\/PRE>\n";}
elsif   (/^\.hd/){print OUTPUT "<PRE>\n";}
elsif   (/^\.he/){print OUTPUT "<\/PRE>\n";}
elsif   (/^\./){}
else    {print OUTPUT;};
&nextline;};

sub doAU
{
	$AU = <INPUT>; chop($AU);
            print OUTPUT <<END;
<BODY>
<A HREF="index.htm"><IMG SRC=../../../rbjgifs/up.gif ALT=UP BORDER=0></A>
<CENTER>
<H1>$TL</H1>
<H3>by $AU</H3>
</CENTER>
END
};

sub doRS
{
print OUTPUT "<DL>\n";
&nextline;
while ($_) {
	if 	(/^\.IP (.*)/) {print OUTPUT "<DT>$1\n<DD>"; &nextline;}
	elsif	(/^\.RE/)	{print OUTPUT "</DL>\n<P>\n"; return;}
	elsif	($_) {&nextstructure;}
	else	{print OUTPUT "</DL>\n<P>\n"; return;}
	};
};

sub translate
{	s/\\fI/<EM>/g;
	s/\\fP/<\/EM>/g;
};

sub windup
{
	print OUTPUT <<END;
<P>
<HR>
<P>
<A HREF="index.htm"><IMG SRC="../../../rbjgifs/up.gif" ALT="UP" BORDER=0></A>
<A HREF="../../index.htm"><IMG SRC="../../../rbjgifs/home.gif" ALT=HOME BORDER=0></A>
&copy; <A HREF="../../rbj.htm"><IMG SRC="../../../rbjgifs/rbjin1.gif" ALT=HOME BORDER=0></A> html converter created $created; modified $modified
</BODY>
</HTML>
END
};
