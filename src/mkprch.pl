# PERL script to create "what's new" from changes list
#$created="1997/6/24";
#$modified="2015-06-28";

$factasia="/usr/local/rbj/share/factasia";
$base=$ARGV[0];
$statdir=$ARGV[1];
#this count determines the filename for this list and the previous one.
#the files included are those which have been modified later than the last list.
$increment=$ARGV[2];
$plistdate=$ARGV[3];
$chlistdate=$ARGV[4];

print "mkprch: \$increment=$increment; \$plistdate=$plistdate; \$chlistdate=$chlistdate\n";

#$previnc=$increment-1;

$destdir="$base/rbjpub/www/column";
$relbase="../../";
$newlist=$statdir."/change$increment.txt";
$chalist=$destdir."/s$chlistdate.htm";

print "      \$chalist: $chalist\n";    

#print "prevlist = $prevlist\n";

if (! -d $base) {die "NOT A DIRECTORY\n";};

#($_,$_,$_,$_,$_,$_,$_,$_,$atime,$prevtime,$ctime,$_,$_) = stat($prevlist);
#print "Prevlist atime:$atime, prevtime:$prevtime, ctime:$ctime\n";
#my($psec,$pmin,$phour,$pmday,$pmon,$pyear,$pwday,$pyday,$pisdst) =
#                                                localtime($ctime);
#print "Prevlist: pyear:$pyear, pmon:$pmon, pmday:$pmday\n";
#<STDIN>;
#$pmon=$pmon+1;
#if ($pyear<100) {$pyear=$pyear+1900};
#print "pmday:$pmday, pmon:$pmon, pyear:$pyear\n";
#$_=<STDIN>;

&classify;

open (CHALIST,"> $chalist");
print CHALIST <<EOF;
<HTML>
<HEAD>
<LINK REL=STYLESHEET TYPE="text/css" HREF="../../prof/p1sty.txt" TITLE="RBJones.com">
<TITLE>What's New at RBJones.com</TITLE>
</HEAD>
<BODY BGCOLOR="#eeffff" CLASS="con">
<A HREF="s000000.htm"><IMG SRC="../../../rbjgifs/up.gif" ALT=UP BORDER=0 ALIGN=LEFT></A>
<CENTER>
<H1>What's New at RBJones.com</H1>
</CENTER>
This page links to the changes in RBJones.com in the last update.
It is generated automatically and omits mention of other automatically generated pages (such as content listings).
<P>
Two tables follow:
<OL>
<LI><A HREF="#new">new pages</A>
<LI><A HREF="#subs">pages whose content has changed</A>
</OL>
<CENTER>
<P>
<A NAME="new"></A>
<H3>new pages</H3>
<TABLE BORDER CELLPADDING=2 CLASS="co2">
<TR><TH>file</TH><TH>title</TH><TH>mdate</TH></TR>
EOF

&proc(0);

print CHALIST <<EOF;
</TABLE>
<P>
<A NAME="subs"></A>
<H3>pages whose content has changed</H3>
<TABLE BORDER CELLPADDING=2 CLASS="co2">
<TR><TH>file</TH><TH>title</TH><TH>mdate</TH></TR>
EOF

&proc(1);

print CHALIST <<EOF;
</TABLE>
<P>
<HR WIDTH="70%">
<A HREF="s000000.htm"><IMG SRC="../../../rbjgifs/up.gif" ALT=up BORDER=0></A>
<A HREF="../../index.htm"><IMG SRC="../../../rbjgifs/home.gif" ALT=home BORDER=0></A>
&copy; <A HREF="../../rbj.htm">
<IMG SRC="../../../rbjgifs/rbjin1.gif" ALT=RBJ ALIGN=absmiddle BORDER=0></A>
</CENTER>
</BODY>
</HTML>
EOF

close CHALIST;

sub classify
{open (NEWLIST,"$newlist");
 %type=(); %title=(); %moddate=();
 while (<NEWLIST>)
 {/^(.*)$/;
  $relfilename = $1;
  if (/^(.*)-m\.(.*)$/) {$frelfilename="$1\.$2"}
  else {$frelfilename=$relfilename};
  $filename = "$base/$relfilename";
# print "\$filename=$filename\n";
# this is the list of files to be ignored
  if (/\/000\.htm/
      || /^rbj03[456]\.htm$/
      || /^www\/column\/s\d+\.htm$/
      || !/.htm(l|)$/
      || /^www\/column\/scurrent.htm/
      || /^www\/column\/shistory.htm/
      || /^philos\/bibliog\/fall2.htm/
      || /^philos\/bibliog\/flogic2.htm/
      || /^philos\/bibliog\/fphil2.htm/
      || /^philos\/bibliog\/freal2.htm/
      || /^philos\/glossary\/fall2.htm/
      )
  {
#  print "omit \$filename=$filename\n";
   next}
  else
  {($_,$_,$_,$_,$_,$_,$_,$_,$_,$thistime,$ctime,$_,$_) = stat($filename);
#  print "A: $atime; T: $thistime; C: $ctime P:$prevtime\n";
   ($_,$_,$_,$tmday,$tmon,$tyear,$_,$_,$_) = localtime($thistime);
   $ftdate=sprintf("%04d-%02d-%02d",$tyear+1900,$tmon+1,$tmday);
   $moddate{$relfilename}=$ftdate;
   ($_,$_,$_,$tmday,$tmon,$tyear,$_,$_,$_) = localtime($ctime);
   $cdate=0;
#  $cdate=sprintf("%04d-%02d-%02d",$tyear+1900,$tmon+1,$tmday);
#  print "file $filename cdate is: $cdate, previous list date:$plistdate\n";
   open (READFILE, $filename);
   $title{$relfilename}="";
   $fmdate=""; $lcvsdate=""; $cvsdate=""; $cvsyear=0; $cvsmonth=0; $cvsday=0;
   while (<READFILE>)
   {if (/<TITLE>([^<]*)<\/TITLE>/) {$title{$relfilename}=$1};
    if (/<title>([^<]*)<\/title>/) {$title{$relfilename}=$1};
    if (/odified:*\s*(\d+)[\/-](\d+)[\/-](\d+)/)
    {$year=$1; $month=$2; $day=$3;
     if ($year<100) {$year=$year+1900};
     $fmdate=sprintf("%04d-%02d-%02d",$year,$month,$day);
#    print "fmdate: $fmdate\n";
#    $_=<STDIN>;
#     if ($type{$relfilename}>0)
#     {if ($plistdate le $fmdate)
#      {$type{$relfilename}=1}
#     };
    };
    if (/reated:*\s*(\d+)[\/-](\d+)[\/-](\d+)/)
    {$cyear=$1; $cmonth=$2; $cday=$3;
     if ($cyear<100) {$cyear=$cyear+1900};
     $cdate=sprintf("%04d-%02d-%02d",$cyear,$cmonth,$cday);
#    print "cdate: $cdate\n";
#    $_=<STDIN>;
    };
    if (/\$Id:[^,]*,v\s*(\d+\.)+\d+\s+(\d+)[\/-](\d+)[\/-](\d+)/)
    {$cvsyear=$2; $cvsmonth=$3; $cvsday=$4;
     if ($cvsyear<100) {$cvsyear=$cvsyear+1900};
     $cvsdate=sprintf("%04d-%02d-%02d",$cvsyear,$cvsmonth,$cvsday);
     if ($lcvsdate lt $cvsdate){$lcvsdate=$cvsdate};
#    print "cvsdate: $cvsdate\n";
#    $_=<STDIN>;
    };
   };
   if ($plistdate le $cdate){
#      print "pd:$plistdate, cd:$cdate, newfile:$relfilename\n";
       $type{$relfilename}=0}
   else	  {
       if ($plistdate le $cvsdate || $plistdate le $fmdate) {$type{$relfilename}=1}
       else {
	   if ($plistdate le $lcvsdate) {$type{$relfilename}=2;
#      print "frelfilename: $frelfilename; plistdate: $plistdate; lcvsdate: $lcvsdate\n"
				     }
	   else {unless (defined($type{$relfilename})) {$type{$relfilename}=3}};
       };
   };
  };
#  $type=$type{$relfilename}; $ftype=$type{$frelfilename};
#  print "relfilename: $relfilename, type: $type, ftype: $ftype\n";
#  print ($relfilename
#	." ".($moddate{$relfilename})
#        ." ".($type{$relfilename})
#	." ".($title{$relfilename})
#	."\n");
 };
#$_=<STDIN>;
 close NEWLIST;
 @filenames=sort(keys %type);
};

sub proc
{my($filetype)=@_;
 foreach $relfilename (@filenames)
 {if (!($type{$relfilename}==$filetype))
	{
	next};
# print "proc-- relfilename: $relfilename, filetype: $filetype\n";
  $filename = "$base/$relfilename";
  $filetitle = $title{$relfilename};
  $filedate = $moddate{$relfilename};
  if ($filedate eq "") {$filedate="\&nbsp;"};
# print "\$relfilename=$relfilename\n";
  if ($filetitle eq "") {
#      print "No title:$relfilename\n";
      next};
  print CHALIST <<EOF;
<TR VALIGN=TOP>
    <TD><A HREF="$relbase$relfilename">$relfilename</A></TD>
    <TD>$filetitle</TD>
    <TD>$filedate</TD>
</TR>
EOF
 };
};

