# PERL script to create list of changed files
#$created="1997/6/16";
#$modified="2007/1/7";

$factasia="/usr/local/rbj/share/factasia";
$base=$ARGV[0];
$statdir=$ARGV[1];
#this count determines the filename for this list and the previous one.
#the files included are those which have been modified later than the last list.
$increment=$ARGV[2];
$plistdate=$ARGV[3];
#$previnc=$increment-1;
#$prevlist=$statdir."/change$previnc.txt";
$newlist=$statdir."/change$increment.txt";
$reldir="";
#$gifdir="rbjgifs";
$relbase="..";
$depth=$ARGV[4];
#$absdir="$base$reldir";
#$statsdir="$factasia/devwww/stats/";

#$dircount=$statsdir."stdh$increment.txt";
#$adircount=$statsdir."stah$increment.txt";

#print "base = $base\n";

if (! -d $base) {die "NOT A DIRECTORY\n";};

#($_,$_,$_,$_,$_,$_,$_,$_,$_,$prevtime,$_,$_,$_) = stat($prevlist);

open (NEWLIST,"> $newlist");

&procdir($reldir, $relbase, $depth);

sub procdir
{my($reldir, $relbase, $depth)=@_;
 my($absdir)=$base;
 if($reldir) {$absdir="$absdir/$reldir";};
 my($lcfile,@dircon,@sdir);
#print "ABS:$absdir, RELD:$reldir, RELB:$relbase, D:$depth\n";
#$indata=<STDIN>;
 opendir (DIR, $absdir);
 @dircon=readdir(DIR);
 closedir DIR;
#foreach $temp (@dircon) {$temp=lc($temp);};
 @sdir=sort(@dircon);
 if ($depth)
   {
    foreach $_ (@sdir)
     {
#      $_=lc $_;
       my($lcdir)=$_;
       $filename="$absdir/$lcdir";
       if ($reldir) {$relfilename="$reldir/$lcdir"}
       else {$relfilename=$lcdir};
       if (/^\./ || /~$/) {next;};
       if (-d $filename)
       { my($subdepth)=$depth-1; my($subreldir)="";
#	 $ifilename="$filename/index.htm";
#        print "\$ifilename:$filename/index.htm ";
#        print "Reldir:$reldir Dir: $_\n";
	 if ($reldir) {$subreldir="$reldir/$lcdir";}
         else         {$subreldir=$lcdir;};
#        print "\$subreldir:$subreldir\n";
         my($subrelbase)="../$relbase";
         &procdir($subreldir, $subrelbase, $subdepth);
       }
       else
       { ($_,$_,$_,$_,$_,$_,$_,$_,$_,$thistime,$_,$_,$_) = stat($filename);
#        print "P: $prevtime; T: $thistime";
	 if (!defined($thistime)) {
	     print "Undefined thistime for file: $filename\n";
	     $thistime=0};
         ($_,$_,$_,$tmday,$tmon,$tyear,$_,$_,$_) = localtime($thistime);
         $cthistime=sprintf("%04d-%02d-%02d",$tyear+1900,$tmon+1,$tmday);
	 open (READFILE, $filename);
	 $fmdate=""; $lcvsdate=""; $cvsdate=""; $cvsyear=0; $cvsmonth=0; $cvsday=0;
	 while (<READFILE>)
	 {if (/odified:*\s*(\d+)[\/-](\d+)[\/-](\d+)/)
	  {$year=$1; $month=$2; $day=$3;
	   if ($year<100) {$year=$year+1900};
	   $fmdate=sprintf("%04d-%02d-%02d",$year,$month,$day);
	  };
# This was an attempt to get the modification date from a PDF file.
# Unfortunately it is just the date the file was last generated.
#	  if (/\/ModDate \(D:(\d\d\d\d)(\d\d)(\d\d)/)
#	  {$year=$1; $month=$2; $day=$3;
#	   if ($year<100) {$year=$year+1900};
#	   $fmdate=sprintf("%04d-%02d-%02d",$year,$month,$day);
#    print "file: $filename \t fmdate: $fmdate\n";
#    $_=<STDIN>;
#     if ($type{$relfilename}>0)
#     {if ($plistdate le $fmdate)
#      {$type{$relfilename}=1}
#     };
#      };
	  if (/\$Id:[^,]*,v\s*(\d+\.)+\d+\s+(\d+)[\/-](\d+)[\/-](\d+)/)
	  {$cvsyear=$2; $cvsmonth=$3; $cvsday=$4;
	   if ($cvsyear<100) {$cvsyear=$cvsyear+1900};
	   $cvsdate=sprintf("%04d-%02d-%02d",$cvsyear,$cvsmonth,$cvsday);
	   if ($cvsdate gt $lcvsdate) {$lcvsdate=$cvsdate};
#    print "cvsdate: $cvsdate\n";
#    $_=<STDIN>;
       };
      };
#	 if ($plistdate le $fmdate || $plistdate le $cvsdate)
#          {print NEWLIST "$relfilename\n";}
	 if ($fmdate gt "") {$cthistime=$fmdate};
	 if ($lcvsdate gt "") {$cthistime=$lcvsdate};
#     print "cthistime: $cthistime\n";
	 if ($plistdate le $cthistime) {print NEWLIST "$relfilename\n"};
     };
   };
};
};
