# PERL script to create an HTML directory index
#$created="1997-03-31";
#$modified="2015-01-08";

#directory to hold listing
$base=$ARGV[0]."/rbjpub";
$statsdir=$ARGV[1];
$base0="$ARGV[0]/$ARGV[2]";

#depth to list
$depth=$ARGV[3];

#this count determines which statistics are included in the directory listing
$increment=$ARGV[4];

print "mkdindex: \$base0=$base0; \$base = $base; \$increment=$increment\n";

$reldir="";
$gifdir="rbjgifs";
$sigfile="rbjpub/rbj.htm";
$relbase="..";
$relgifdir="$relbase/$gifdir";
$longcname="rbj034.htm";

$dircount="$statsdir/stdh$increment.txt";
$adircount="$statsdir/stah$increment.txt";

if (! -d $base) {die "NOT A DIRECTORY\n";};
if (! -d $base0) {die "NOT A DIRECTORY\n";};

open (OUTLONG,"> $base/$longcname");

%hits=load2($dircount);
%ahits=load2($adircount);

print OUTLONG <<EOM;
<HTML><HEAD>
<LINK REL=STYLESHEET TYPE="text/css" HREF="prof/p1sty.txt" TITLE="RBJones.com">
<TITLE>RBJones.com Directory Listing</TITLE>
<META name="description" content="A listing of the RBJones.com directory structure with links to the content pages.">
<META name="keywords" content="RbJ FactasiA ContenT">
</HEAD>
<BODY CLASS=con>
<CENTER><H1>RBJones.com Directory Listing</H1>

<TABLE WIDTH="70%"><TR VALIGN=TOP><TD WIDTH="50%">
<TABLE CLASS=co2><TR><TD>
This is a list of the filestore directories at the RBJones.com site.
Each directory is hyper-linked to a main page for that directory (index.htm[l]) and to a full directory content listing (000.htm).
</TD></TR></TABLE>
</TD><TD WIDTH="50%">
<TABLE CLASS=co2>
<TR VALIGN=TOP><TH>col</TH><TH>description</TH></TR>
<TR VALIGN=TOP><TH>pgs</TH><TD>number of files in directory</TD></TR>
<TR VALIGN=TOP><TH>size</TH><TD>total of file sizes</TD></TR>
<TR VALIGN=TOP><TH>hits</TH><TD>hits on files in directory over one calendar week</TD></TR>
<TR VALIGN=TOP><TH>agg</TH><TD>hits on files in directory and subdirectories</TD></TR>
</TABLE>
</TD></TR></TABLE>

<P>
<TABLE CLASS=co2>
<TR VALIGN=TOP><TD><B>full contents</B></TD><TD><B>main</B></TD>
<TD><B>title</B></TD><TD><B>pgs</B></TD><TD ALIGN=RIGHT><B>size</B></TD>
<TD><B>hits</B></TD><TD><B>agg</B></TD>
</TR>
EOM

&procdir($reldir, $relbase, $depth);

print OUTLONG <<EOF;
</TABLE>
<CENTER>
<HR WIDTH="70%">
<A HREF="$relbase/index.htm"><IMG SRC="$relgifdir/home.gif" BORDER=0 ALIGN=ABSMIDDLE ALT=home></A>
<A HREF="$relbase/$sigfile"><IMG SRC="$relgifdir/rbjin1.gif" BORDER=0 ALIGN=ABSMIDDLE ALT=rbj></A>
</CENTER>
</BODY>
</HTML>
EOF

sub procdir
{my($reldir, $relbase, $depth)=@_;
 my($absdir)=$base0;
 if($reldir) {$absdir="$absdir/$reldir";};
 my($lcfile,@dircon,@sdir);
#print "ABS:$absdir, RELD:$reldir, RELB:$relbase, D:$depth\n";
#$indata=<STDIN>;
 opendir (DIR, $absdir);
 @dircon=readdir(DIR);
 closedir DIR;
# print @dircon;
# $_=<STDIN>;
# foreach $temp (@dircon) {$temp=lc($temp);};
 @sdir=sort(@dircon);
# print @dircon;
# $_=<STDIN>;
 if ($depth)
   {
    foreach $_ (@sdir)
     { $_=lc $_; my($lcdir)=$_;
       $filename="$absdir/$lcdir";
       if (/^\./ || /~$/) {next;};
       if (-d $filename)
       { my($subdepth)=$depth-1; my($subreldir)="";
         &filecount;
	 $ifilenamee="index.htm";
	 $ifilename="$filename/index.htm";
	 if ((! -f "$ifilename") && -f ("$ifilename"."l")) {
	     $ifilename =$ifilename."l";
	     $ifilenamee=$ifilenamee."l"
	 };
#        print "\$ifilename:$ifilename; \$ifilenamee:$ifilenamee;\n";
	 &gettitle;
#        print "Reldir:$reldir Dir: $_\n";
	 if ($reldir) {$subreldir="$reldir/$lcdir";}
         else         {$subreldir=$lcdir;};
#        print "\$subreldir:$subreldir\n";
         my($subrelbase)="../$relbase";
         my($dirfile)="$lcdir/000.htm";
	 my($confile)="$lcdir/$ifilenamee";
# 	 print "\$lcdir: $lcdir ";
	 my($dhits)=$hits{"/rbjpub/$subreldir/"};
	 if (! defined ($dhits)) {$dhits=0};
	 my($adhits)=$ahits{"/rbjpub/$subreldir/"};
	 if (! defined ($adhits)) {$adhits=0};
	 if ($dhits==$adhits) {$adhits="";};
# 	 print "\$dhits $dhits \$adhits $adhits\n";
	 my($reldirns)="$lcdir";
         if($reldir) {	$dirfile="$reldir/$dirfile";
			$confile="$reldir/$confile";
			$reldirns="$reldir/$reldirns";};
	 $reldirns="$base0$reldirns";
	 $reldirns=~s/^\///;
	 $reldirns=~s/\//\%2F/g;
#	 print "$reldir/$lcdir\t$subreldir\n";
         print OUTLONG <<EOF;
<TR VALIGN=TOP><TD><A HREF="$dirfile">$subreldir</A></TD>
EOF
	if (-f "$ifilename")	{print OUTLONG <<EOF;
<TD><A HREF="$confile">index</A></TD><TD>$title</TD><TD ALIGN=RIGHT>$filecount</TD>
<TD ALIGN=RIGHT>$dirsize</TD><TD ALIGN=RIGHT>$dhits</TD><TD ALIGN=RIGHT>$adhits</TD>
</TR>
EOF
					}
	else 				{print OUTLONG <<EOF;
<TD>&nbsp;</TD><TD>&nbsp;</TD><TD ALIGN=RIGHT>$filecount</TD><TD ALIGN=RIGHT>$dirsize</TD>
<TD ALIGN=RIGHT>$dhits</TD><TD ALIGN=RIGHT>$adhits</TD>
</TR>
EOF
					};
         &procdir($subreldir, $subrelbase, $subdepth);
       };
     };
   };
};

sub gettitle
{$title="";
 if (-f $ifilename)
 { open (INFILE, $ifilename);
   while (<INFILE>)
   {if (/<TITLE>(.*)$/i)
      { $title="";
        $_=$1;
        do  
        { if (/([^<]*)<\/TITLE>/i)
            { $title=$title.$1;
	      last;
	    };
          $title=$title.$_;
          $_=<INFILE>;
        } while (!eof(INFILE));
#       print "$title\n";
	last;};
   };
   close INFILE;
 };
};

sub filecount
{ my($temp,$filesize);
  opendir (DIR2, $filename);
  my(@dircon)=readdir(DIR2);
  $filecount=0; $dirsize=0;
  closedir DIR2;
  foreach $temp (@dircon)
    {$ltemp=lc($temp);
     if ($ltemp=~/\.(htm|html|pdf)$/)
       {++$filecount;
        ($_,$_,$_,$_,$_,$_,$_,$filesize,$_,$_,$_,$_,$_) = stat("$filename/$temp");
	if(!defined($filesize)){
	    print "unknown filesize for file: $filename/$temp\n";
	    $filesize=0};
        $dirsize+=$filesize;
       };
    };
};

sub load2
{	my($file)=shift;
	my(%pages);
	open(INPUT, $file);
	while (<INPUT>)
	{if (/^(\d*)\s+(.*)$/)	{$pages{$2}=$1;}
	};
	close INPUT;
	%pages
};



