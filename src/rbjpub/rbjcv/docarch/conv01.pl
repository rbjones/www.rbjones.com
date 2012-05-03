# $Id: conv01.pl,v 1.2 2012/05/03 20:44:06 rbj Exp $
# For converting .txt files of roff source into HTM files
$created="5/7/95";
$updated="6/7/95";
$file=$ARGV[0];
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
elsif   (/^\.IP/){print OUTPUT "<P>\n";}
elsif   (/^\.LP/){print OUTPUT "<P>\n";}
elsif   (/^\.NH \d*/){$NH = $1; $HL=2+$1; print "$HL\n"; $HDNG=<INPUT>;
                chop($HDNG);
                print OUTPUT "<CENTER><H$HL>$HDNG</H$HL></CENTER>\n";}
elsif   (/^\.NH/){$HDNG=<INPUT>; chop($HDNG);
                print OUTPUT "<CENTER><H2>$HDNG</H2></CENTER>\n";}
elsif   (/^\.RS/){&doRS;}
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
</BODY><P>
<HR>
<P>
<A HREF="000.htm"><IMG SRC="../../../rbjgifs/z.gif" ALT="Z" BORDER=0></A>
<A HREF="index.htm"><IMG SRC="../../../rbjgifs/up.gif" ALT="UP" BORDER=0></A>
<A HREF="../../index.htm"><IMG SRC="../../../rbjgifs/home.gif" ALT=HOME BORDER=0></A>
<A HREF="../../help/index.htm"><IMG SRC="../../../rbjgifs/help.gif" ALT=HELP BORDER=0></A>
&copy; <A HREF="../../rbj.htm">Roger Bishop Jones</A> converted to html:  6/7/95 modified 6/7/95
END
};
