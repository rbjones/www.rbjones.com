# PERL script to create an HTML index

#$created="1997-03-31";
#$modified="2015-06-28";
#print "created $created modified $modified ";

$factasia="/usr/local/rbj/share/factasia";
$relbase="..";
$base="$ARGV[0]/";
$statsdir="$ARGV[1]/";
$reldir=$ARGV[2];
$increment=$ARGV[3];

print "mkindex: \$statsdir=$statsdir; \$reldir=$reldir; \$increment=$increment\n";

$gifdir="rbjgifs";
$sigfile="rbjpub/rbj.htm";
$adepth=3;
$hotdepthlimit=0;
$absdir=$base.$reldir;

$hitcount=$statsdir."stdif_n$increment.txt";
$adircount=$statsdir."stah$increment.txt";

#print "absdir = $absdir\n";

if (! -d $absdir) {die "NOT A DIRECTORY\n";};

%hits=load2($hitcount);
%ahits=load2($adircount);

&procdir($reldir, $relbase, $adepth);

sub procdir
{my($reldir, $relbase, $depth)=@_;
 my($absdir)=$base.$reldir;
 my($lcfile,@dircon,@sdir);
#print "ABS:$absdir, RELD:$reldir, RELB:$relbase, D:$depth\n";
#$indata=<STDIN>;
 opendir (DIR, $absdir) || die "open $absdir failed";
 @dircon=readdir(DIR);
 closedir DIR;
#print "DIRCON: @dircon\n";
#foreach $temp (@dircon) {$temp=lc($temp);};
 @sdir=sort(@dircon);
#print "SDIR: @sdir\n"; $temp=<STDIN>;
 if ($depth)
   {foreach $_ (@sdir)
     { 
#      $_=lc $_;
       $filename="$absdir/$_";
       if (/^\./) {next;};
       if (-d $filename)
       { my($subdepth)=$depth-1;
         my($subreldir)="$reldir/$_";
         my($subrelbase)="../$relbase";
         &procdir($subreldir, $subrelbase, $subdepth);
       };
     };
   };

 open (OUTPUT,"> $absdir/000.htm") || die "failed to create $absdir/000.htm";
 print OUTPUT <<EOM;
<HTML><HEAD>
<TITLE>Index for directory $reldir</TITLE>
<LINK REL=STYLESHEET TYPE="text/css" HREF="$relbase/rbjpub/prof/p1sty.txt" TITLE="RBJones.com">
<META name="description" content="Index of subdirectories and files in directory $reldir of RBJones.com.">
<META name="keywords" content="RbJ RBJones.com IndeX">
</HEAD>
<BODY CLASS=con BGCOLOR="#eeffff">
EOM
if ($adepth>$depth)
{ print OUTPUT <<EOM;
<A HREF="../000.htm"><IMG SRC="$relbase/$gifdir/up.gif" BORDER=0 ALIGN=LEFT ALT=UP></A>
EOM
};
print OUTPUT <<EOM;
<CENTER><H1>Contents of RBJones.com directory: $reldir</H1>
EOM
 if ($depth>$hotdepthlimit)
 {
# print "Depth:$depth $hotdepthlimit\n";
#  print OUTPUT <<EOM;
#<FORM method="get" action="http://www.hotbot.com/">
#<INPUT TYPE="hidden" NAME="_v" VALUE="2">
#<A HREF="http://www.hotbot.com/">
#<IMG SRC="$relbase/rbjgifs/hotbot2.gif"	width=105 height=34 alt="HotBot" border=0></A>
#    Search directory $reldir for:
#    <INPUT type=text NAME="MT" SIZE=25 VALUE="" MAXLENGTH=100>
#    <INPUT type=image
#    src="$relbase/rbjgifs/hbsrch.gif"
#    name="act.search"
#    alt="search"
#    value="Submit Search" width=78 height=29 border=0>
#<INPUT TYPE="hidden" NAME="MANY"
#EOM
#  print OUTPUT "VALUE=\"HdB {+domain:www.rbjones.com";
#  $tempdollar=$_;
#  $_=$reldir;
#  while ($_)
#  {if(s/([^\/]*)\/(.*)/$2/)
# 	{print OUTPUT " +originurlpath:$1"}
#   else	{print OUTPUT " +originurlpath:$_"; $_=""};
#  };
# $_=$tempdollar;
# print OUTPUT <<EOM;
#} HdD {directory $reldir of www.rbjones.com}">
#</FORM>
 };
 print OUTPUT <<EOM;
</CENTER>

Hit figures shown are for one calendar month.
<P>
This directory contains the following subdirectories:
<CENTER><TABLE CLASS="co2">
<TR><TH ALIGN=LEFT WIDTH=100>directory</TH><TH ALIGN=RIGHT WIDTH=100>hits</TH></TR>
EOM

 foreach $_ (@sdir)
  {$filename="$absdir/$_";
   if (/^\./ || /~$/) {next;};
   $lcfile=$_;
   if (-d $filename)
     {$dirpath="/$reldir/$_/";
#     print "Dirpath: $dirpath, ";
      $dirhitcount=$ahits{$dirpath};
      if (! defined($dirhitcount))
	{$dirhitcount=0;
	print "undefined dirhitcount for directory: $dirpath\n"
	};
#     print "Dirhitcount: $dirhitcount\n";
      print OUTPUT <<EOF;
<TR><TD><A HREF="$lcfile/000.htm">$lcfile</A></TD><TD ALIGN=RIGHT>$dirhitcount</TD></TR>
EOF
     };
  };

 print OUTPUT <<EOF;
</TABLE></CENTER>
<P>
and the following files:
<TABLE CELLPADDING=2 WIDTH="100%" CLASS="co2">
<TR><TH>name</TH><TH>title</TH><TH ALIGN=RIGHT>size</TH><TH ALIGN=RIGHT>hits</TH><TH>mdate</TH></TR>
EOF

 foreach $_ (@sdir)
  {
#  $_=lc $_;
   if (/^000\.htm/ || /^\..*/ || /~$/) {next;};
#  if (!/\.htm/) {next;};
   $filename="$absdir/$_";
   my($filepath)="/$reldir/$_";
   $lcfile=$_;
   if (-f $filename)
     {&gettitle;
      my($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
         $atime,$mtime,$ctime,$blksize,$blocks)
           = stat($filename);
      my($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) =
                                                localtime($mtime);
#     print "File:$filename, Time:$ctime, $mday, $mon, $year, $wday, $yday, $isdst\n";
#     $temp=<STDIN>;
      $mon=$mon+1;
#     print "Filepath: $filepath, ";
      $filehitcount=$hits{$filepath};
      if (! (defined($filehitcount))) {$filehitcount=""};
#     print "Filehitcount: $filehitcount\n";
      $filemdate=sprintf("%02d-%02d-%02d",$year+1900,$mon,$mday);
      print OUTPUT <<EOF;
<TR VALIGN=TOP><TD><A HREF="$lcfile">$lcfile</A></TD><TD>$title</TD><TD ALIGN=RIGHT>$size</TD><TD ALIGN=RIGHT>$filehitcount</TD><TD>$filemdate</TD></TR>
EOF
     };
  };

 print OUTPUT <<EOF;
</TABLE>
<CENTER>
<HR WIDTH="70%">
EOF
if ($adepth>$depth)
{  print OUTPUT <<EOF;
<A HREF="../000.htm"><IMG SRC="$relbase/$gifdir/up.gif" BORDER=0 ALT=up></A>
EOF
};
print OUTPUT <<EOF;
<A HREF="$relbase/rbjpub/index.htm"><IMG SRC="$relbase/$gifdir/home.gif" BORDER=0 ALIGN=ABSMIDDLE ALT=home></A>
<A HREF="$relbase/$sigfile"><IMG SRC="$relbase/$gifdir/rbjin1.gif" BORDER=0 ALIGN=ABSMIDDLE ALT=rbj></A>
00-00-00
</CENTER>
</BODY>
</HTML>
EOF
};

sub gettitle
{$title="...";
 if ($filename =~ /\.pdf$/) {return $title};
 open (INFILE, $filename) || die "failed to open $filename";
 while (<INFILE>)
 {if (/.TITLE>(.*)$/i)
    { $title="";
      $_=$1;
      do  
      { if (/([^<!]*).\/TITLE>/i)
          { $title=$title.$1;
	    last;
	  };
        $title=$title.$_;
        $_=<INFILE>;
      } while (!eof(INFILE));
#     print "$title\n";
      last;};
 };
 close INFILE;
};

sub load2
{	my($file)=shift;
	my(%pages);
	open(INPUT, $file) || die "failed to open $file";
	while (<INPUT>)
	{if (/^(\d*)\s+(.*)$/)	{$pages{$2}=$1;}
	};
	close INPUT;
	%pages
};


