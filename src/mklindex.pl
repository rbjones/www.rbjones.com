# PERL script to create a long HTML content page

#$created="1997-03-31";
#$modified="2007-01-07";

$base="$ARGV[0]/$ARGV[1]";

print "mklindex: \$base=$base\n";

$reldir="";
$gifdir="rbjgifs";
$sigfile="rbjpub/rbj.htm";
$relbase="..";
$depth=2;
#$absdir="$base$reldir";
$longcname="0000.htm";

#print "base = $base\n";

if (! -d $base) {die "NOT A DIRECTORY: $base\n";};

open (OUTLONG,"> $base/$longcname") || die "failed to create $base/$longcname";

print OUTLONG <<EOM;
<HTML><HEAD>
<LINK REL=STYLESHEET TYPE="text/css" HREF="$relbase/rbjpub/prof/p1sty.txt" TITLE="RBJones.com">
<TITLE>Full RBJones.com Content Listing</TITLE>
<META name="description" content="Almost complete content listing of RBJones.com.">
<META name="keywords" content="RbJ FactasiA ContenT">
</HEAD>
<BODY CLASS="con" BGCOLOR="#eeffff">
<CENTER><H1>Full RBJones.com Content Listing</H1></CENTER>
This listing covers the first 3 directory levels of RBJones.com.
The next level contains the largest directories consisting of hypertext editions of classic philosophical works, for which separate listings are linked to.
<P>
Directory structure:
<P>
EOM

&procdir($reldir, $relbase, $depth);
&procdir2($reldir, $relbase, $depth);

print OUTLONG <<EOF;
</TABLE>
<CENTER>
<HR WIDTH="70%">
<A HREF="$relbase/index.htm"><IMG SRC="$relbase/$gifdir/home.gif" BORDER=0 ALIGN=ABSMIDDLE ALT=home></A>
<A HREF="$relbase/$sigfile"><IMG SRC="$relbase/$gifdir/rbjin1.gif" BORDER=0 ALIGN=ABSMIDDLE ALT=rbj></A>
</CENTER>
</BODY>
</HTML>
EOF
close OUTLONG;

sub procdir
{my($reldir, $relbase, $depth)=@_;
 my($absdir)=$base;
 if($reldir) {$absdir="$absdir/$reldir";};
 my($lcfile,@dircon,@sdir);
#print "$absdir, $relbase, $depth\n";
#$indata=<STDIN>;
 opendir (DIR, $absdir) || die "failed to open directory $absdir";
 @dircon=readdir(DIR);
 closedir DIR;
#foreach $temp (@dircon) {$temp=lc($temp);};
 @sdir=sort(@dircon);
    print OUTLONG "<FONT SIZE=2><UL>\n";
    foreach $_ (@sdir)
     { $lcdir=lc $_; $_=$lcdir;
       $filename="$absdir/$_";
       if (/^\./ || /~$/) {next;};
       if (-d $filename)
       { my($subdepth)=$depth-1; my($subreldir)="";
#        print "Reldir:$reldir Dir: $_\n";
	 if ($reldir) {$subreldir="$reldir/$_";}
         else         {$subreldir=$_;};
#        print "$subreldir\n"; $input=<STDIN>;
         my($subrelbase)="../$relbase";
         my($dirfile)="$_/000.htm";
	 my($diradd)="$lcdir";
         if($reldir) {$dirfile="$reldir/$dirfile"; $diradd="$reldir/$lcdir";};
	 if($depth) {$diradd=~s/\//_/; $diradd="#$diradd";}
         else       {$diradd="$diradd/000.htm"};
         print OUTLONG <<EOF;
<LI><A HREF="$diradd">$_</A>
EOF
         &procdir($subreldir, $subrelbase, $subdepth);
       };
     };
   print OUTLONG "</UL></FONT>\n";
};

sub procdir2
{my($reldir, $relbase, $depth)=@_;
 my($absdir)=$base;
 if($reldir) {$absdir="$absdir/$reldir";};
 my($lcfile,@dircon,@sdir);
 my($aname)=$reldir;
 $aname=~s/\//_/;
#print "$absdir, $relbase, $reldir, $aname, $depth\n";
#$indata=<STDIN>;
 opendir (DIR, $absdir) || die "failed to open directory $absdir";
 @dircon=readdir(DIR);
 closedir DIR;
 foreach $temp (@dircon) {$temp=lc($temp);};
 @sdir=sort(@dircon);
 print OUTLONG <<EOF;
<A NAME="$aname"></A>
<LI>
EOF
 if (-f "$absdir/index.htm") {
  print OUTLONG <<EOF;
<A HREF="./$reldir/index.htm">$reldir</A>
EOF
  }
 elsif (-f "$absdir/index.html") {
  print OUTLONG <<EOF;
<A HREF="./$reldir/index.html">$reldir</A>
EOF
  }
 else {
  print OUTLONG <<EOF;
<A HREF="./$reldir/000.htm">$reldir</A>
EOF
 };
 print OUTLONG <<EOF;
<P>
<TABLE ALIGN=CENTER BORDER CELLPADDING=2 CLASS="co2">
<TR><TH>name</TH><TH>size</TH><TH>mdate</TH><TH>title</TH></TR>
EOF

@sdirsave=@sdir;

 foreach $_ (@sdir)
  {$_=lc $_; $lcfile=$_;
   if (/^\./ || /~$/) {next;};
   if (!(/\.htm(l|)/ || /\.pdf/ || //)) {next;};
   $filename="$absdir/$_";
   if (-f $filename)
     {&gettitle;
      my($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
         $atime,$mtime,$ctime,$blksize,$blocks)
           = stat($filename);
      my($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) =
                                                localtime($mtime);
      $mon=$mon+1;
      $mdatead=sprintf("%04d-%02d-%02d",$year+1900,$mon,$mday);
      my($lcfileref)=$lcfile;
      if($reldir){$lcfileref="$reldir/$lcfile";};
      if(!$title){$title="&#160;";};
      print OUTLONG <<EOF;
<TR VALIGN=TOP><TD><A HREF="$lcfileref">$lcfile</A></TD><TD ALIGN=RIGHT>$size</TD><TD>$mdatead</TD><TD>$title</TD></TR>
EOF
     };
  };

 print OUTLONG <<EOF;
</TABLE>
<P>
EOF

@sdir=@sdirsave;

 if ($depth)
   {foreach $_ (@sdir)
     { $_=lc $_;
       $filename="$absdir/$_";
       if (/^\./) {next;};
#      print "\$filename=$filename\n";
       if (-d $filename)
       { my($subdepth)=$depth-1; my($subreldir)="";
	 if ($reldir) {$subreldir="$reldir/$_";}
         else         {$subreldir=$_;};
         my($subrelbase)="../$relbase";
         &procdir2($subreldir, $subrelbase, $subdepth);
       };
     };
   };

};

sub gettitle
{$title="";
 open (INFILE, $filename) || die "unable to open file $filename";
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
#     print "$title\n";
      last;};
 };
 close INFILE;
};

