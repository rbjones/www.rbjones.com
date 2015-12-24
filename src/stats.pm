package stats;
#$created="1996/11/16";
#$modified="2000/8/11";

$sourcehome="/usr/local/rbj/share/factasia/www";

sub clean
{	my($pathname)=shift;
	$pathname=~s/\/www.rbjones.com//;
	$pathname=~s/liebniz/leibniz/;
	$pathname=~s/\/\//\//;
	while ($pathname=~s/\/[^\/]*\/\.\.\//\//) {};
	while ($pathname=~s/\/\.\//\//) {};
	while ($pathname=~s/\/\///) {};
	$pathname
};

sub diff
{	my($pages1, $pages2)=@_;
#	print "\n===========\nDiff\n";
	my(%pages,$newcount);
	foreach $key (keys %$pages1)
		{
#		print "$key:";
		$newcount=$$pages1{$key};
#		print "$newcount ::";
		if (defined ($$pages2{$key}))
		  {$newcount-=$$pages2{$key};};
#		print " $newcount\n";
		$pages{$key}=$newcount;
		}
#	print "\n";
	%pages
};

sub dirhits
{	my($pages)=@_;
	my(%dpages,$count,$agcount,$dirpath,$filename);
	foreach $key (keys %$pages)
	{if ($key=~/(\/([^\/]*\/)*)(.*)$/)
	 {$dirpath=$1; $filename=$3;
	  $count=$$pages{$key};
	  if (!(defined ($dpages{$dirpath}))) {$dpages{$dirpath}=0;};
	  $agcount=($dpages{$dirpath}+=$count);
#	  print "Key:$key, Dir:$dirpath, File:$filename, Count:$count, Agg:$agcount\n";
	 };
	};
	%dpages
};

sub agdirhits
{	my($dirhits)=@_;
	my(%adhits,$agcount);
	foreach $key (keys %$dirhits)
	{$adhits{$key}=0;
	 foreach  $key2 (keys %$dirhits)
	 {
#	   print "Key:$key, Key2:$key2\n";
	     if (length ($key) <= length ($key2)
		 && substr ($key2, 0, length($key)) eq $key)
	  {
	   $agcount=($adhits{$key}+=$$dirhits{$key2});
#	   print "Key:$key, Key2:$key2; $agcount\n";
	  };
         };
	};
	%adhits
};

sub load
{	my($file)=shift;
	my(%pages);
	open(INPUT, $file) || die "failed to open $file";
	while (<INPUT>)
	{if (/pages:([^:]*):(\d+)/)
		{	$path=&clean($1);
			if (defined($pages{$path}))
			  {$pages{$path}+=$2;}
			else
			  {$pages{$path}=$2};
#			print "$path,$oldcount,$2\n"
		}
	};
	close INPUT;
	%pages
};

# this variant is for loading files of format "count path" without
# duplicate paths
sub load2
{	my($file)=shift;
	my(%pages);
	open(INPUT, $file) || die "failed to open $file";
	while (<INPUT>)
	{if (/^(\d*)\s+(.*)$/)	{$pages{$path}=$1;}
	};
	close INPUT;
	%pages
};

# This variant for loading stats files from digitalspace.
# Multiple input files are processed.
sub load3
{	my($file)=shift;
	my(%pages);
	while($file)
 	{
		print "opening $file\n";
		open(INPUT, $file) || die "load3 failed to open file: $file";
		while (<INPUT>)
		{if (/GET\s+([^\s]*)\s/)
			{	$path=&clean($1);
				if (defined($pages{$path}))
				  {$pages{$path}+=1;}
				elsif ($path=~/\.htm$/)
				  {$pages{$path}=1};
#				print "$path,$oldcount,$2\n"
			}
		};
		close INPUT;
		$file=shift;
	};	
	%pages
};

# This variant for loading stats file from interserver.
sub load4
{	my($file)=@_;
	my(%pages);
#		print "opening $file ($month, $year)\n";
		open(INPUT, $file) || die "load4 failed to open file: $file";
		while (<INPUT>)
		{if (/GET\s+([^\s]*)\s/)
			{	$path=&clean($1);
#				print "$path\n";
				if (defined($pages{$path})) {
#				   print "$path\n";
				   $pages{$path}+=1;}
				elsif ($path=~/\.(html|htm|pdf)$/) {
#				  print "$path\n";
				  $pages{$path}=1};
#				print "$path,$oldcount,$2\n"
			}
      		};
		close INPUT;
		$file=shift;
	%pages
};

# This variant for loading stats file from interserver (another version)
# This one does not expect to find a complete month of stats but will take
# any number of complete days of stats.
sub load5
{	my($file)=@_;
	my(%pages);
#		print "opening $file ($month, $year)\n";
		open(INPUT, $file) || die "load4 failed to open file: $file";
	        $days=0; $previousday=0;
	        while (<INPUT>)
		{if (/[(\d+)[^]]*] "GET/) {
		    $day=$1;
		    if (! $day == $previousday) {$days+=1; $previousday=$day};
		    if (/GET\s+([^\s]*)\s/)
			{	$path=&clean($1);
#				print "$path\n";
				if (defined($pages{$path})) {
#				   print "$path\n";
				   $pages{$path}+=1;}
				elsif ($path=~/\.htm(l|)$/) {
#				  print "$path\n";
				  $pages{$path}=1};
#				print "$path,$oldcount,$2\n"
			}
		    };
		};
		close INPUT;
		$file=shift;
	        $pages2={};
	        foreach $key($pages) {
		$pages2{$key}=int($pages{$key}*7/$days)};
	%pages2
};

sub outal
{	my($file, %pages)=@_;
	open(OUTPUT, "> $file") || die "failed to create file $file";
	print OUTPUT <<EOF;
<HTML><HEAD><TITLE>Alphabetic Hit Count</TITLE></HEAD>
<BODY BGCOLOR="#ffcccc">
<PRE>
EOF
	@keylist=(sort (keys %pages));
	my($total)=0;
	foreach $key (@keylist)
	   {	
#		print "$key:";
		$count=$pages{$key};
#		if (!$count) {print "NOT DEFINED:$key:$count\n"; $temp=<STDIN>};
#		print "$count\n";
 		print OUTPUT "$count\t<A HREF=\"..$key\">$key</A>\n"; $total+=$count};
		print OUTPUT <<EOF;
</PRE>
<HR WIDTH="70%">
</BODY>
</HTML>
EOF
	close OUTPUT;
	$total
};

sub makeag
{	my($file, %pages)=@_;
	open(OUTPUT, "> $file") || die "failed to create file $file";
	print OUTPUT <<EOF;
<HTML><HEAD><TITLE>Aggregated Hit Counts</TITLE></HEAD>
<BODY BGCOLOR="#f0e0e0">
<PRE>
EOF
	@keylist=(sort (keys %pages));
	my($total)=0;
	foreach $key (@keylist)
	   {$count=$pages{$key};
            print OUTPUT "$count\t<A HREF=\"..$key\">$key</A>\n"; $total+=$count};
	print OUTPUT <<EOF;
</PRE>
<HR WIDTH="70%">
</BODY>
</HTML>
EOF
	close OUTPUT;
	$total
};

sub outnu
{	my($file, %pages)=@_;
	open(OUTPUT, "> $file") || die "failed to create file $file";
#       print "output to $file\n";
	@keynames=(keys %pages);
	@keylist=sort {$pages{$b} <=> $pages{$a}} @keynames;
	my($total)=0; my($pagecount)=0;
	foreach $key (@keylist)
		{$count=$pages{$key};
		 $pagecount++;
		 print OUTPUT "$count\t$key\n";
		 $total+=$count}
	print OUTPUT "$total\t(total)";
	close OUTPUT;
	$pagecount
};

sub outtop100
{	my($total, $pagecount, $file, $pfile, $ot100, $nt100, %pages)=@_;
#	print "File:$file; NT100:$nt100; OT100:$ot100\n";
	my(%oldpages, $oldpos, %titles, $originalcount);
	open(OT100, "$ot100") || die "failed to open file $ot100";
	while(<OT100>) {/(\d+):(.*)/; $oldpages{$2}=$1;
#		    print ("oldpage: $2 is:".($oldpages{$2})."\n")
		    };
#	print "OLDPAGES\n%oldpages";
	close OT100;
	open(OUTPUT, "> $file") || die "failed to create file $file";
	open(NT100, "> $nt100") || die "failed to create file $nt100";
	print OUTPUT <<EOF;
<HTML><HEAD>
<LINK REL=STYLESHEET TYPE="text/css" HREF="prof/p1sty.txt" TITLE="Factasia">
<TITLE>RBJones.com Top 100</TITLE>
</HEAD>
<BODY CLASS=con>
<CENTER><H1>RBJones.com Top 100</H1>
<FONT SIZE=2>
Hit figures shown against each page are for one calendar month.
<BR>
Total number of hits over the month (excluding graphics) = $total over $pagecount pages.
<BR>
<A HREF="rbj035.htm">best previous</A>
</FONT>
<TABLE CLASS=con>
<TR><TD COLSPAN=2><B>posn</B></TH><TH>hits</TH><TH>filename</TH><TH>title</TH></TR>
EOF
	@keynames=(keys %pages);
	@keylist=sort {$pages{$b} <=> $pages{$a}} @keynames;
#	print @keylist;
#	print (keys %oldpages);
	my($total100)=0; my($count100)=0; my(%donekeys)=(); my(%entrydata)=();
	my($oldkey)=0;
	toploop: foreach $key (@keylist)
		{$count=$pages{$key};
		 $originalcount=0;
#		 print "Pos: $count100; Count: $count; Key: $key\n"; 
                 if($key!~/\.htm(l|)/) {next toploop};
                 if($key=~/\/prof\//) {next toploop};
                 if($key=~/^\/index.htm/) {next toploop};
                 if($key=~/glossary\/fall2.htm$/) {next toploop};
                 if($key=~/^\/$/) {next toploop};
		 $key=~s/-(m|i)//;
		 if(defined($donekeys{$key})){next toploop};
		 $donekeys{$key}=$count;
                 my($ifilename)=$sourcehome.$key;
		 my($title)=&gettitle($ifilename);
#		 print "Title: $title\n";
                 if($title eq ""
			|| $title=~/Index[Ff]rame:/) {next toploop};
                 if($title=~/Main[Ff]rame:\W*(.*)/) {
		     $title=$1;
#		     print "Mainframe title:$title\n";
		     if (defined($titles{$title})) {
			 next toploop}
		     else {$titles{$title}=$count100};
		 }
		 else {
		     if (defined($titles{$title})) {
			 $originalcount=$titles{$title}+1;
			 $oldkey=$entrydata{$originalcount}{key};
#			 print "Entrydata: num=$originalcount oldkey=$oldkey newkey=$key\n";
			 $entrydata{$originalcount}{key}=$key;
			 $oldpos=$oldpages{$key};
			 if (!(defined($oldpos))) {
			     $oldpos="-"; $change="*";
			     $direc="<IMG SRC=\"../rbjgifs/sup.gif\" ALT=up>"
			 }
			 else {$change=$originalcount-$oldpos;
			       if ($change>0) {
				   $direc="<IMG SRC=\"../rbjgifs/sdown.gif\" ALT=down>"
			       }
			       elsif ($change<0) {
				   $change=-$change;
				   $direc="<IMG SRC=\"../rbjgifs/sup.gif\" ALT=up>"
			       }
			       elsif ($change==0) {$change=" "; $direc=" "}
			 };
			 $entrydata{$originalcount}{direc}=$direc;
			 $entrydata{$originalcount}{change}=$change;
			 next toploop}
		     else {$titles{$title}=$count100};
		 };
		 $count100++;
		 $oldpos=$oldpages{$key};
#		 print "OLDPAGE at $oldpos is $key\n";
		 if (!(defined($oldpos))) {
			$oldpos="-"; $change="*";
			$direc="<IMG SRC=\"../rbjgifs/sup.gif\" ALT=up>"
			}
		 else {$change=$count100-$oldpos;
			if ($change>0) {
				$direc="<IMG SRC=\"../rbjgifs/sdown.gif\" ALT=down>"
				}
			elsif ($change<0) {
				$change=-$change;
				$direc="<IMG SRC=\"../rbjgifs/sup.gif\" ALT=up>"
				}
			elsif ($change==0) {$change=" "; $direc=" "}
			};
		 $entrydata{$count100}={direc=>$direc,change=>$change,count=>$count,key=>$key,title=>$title};
		 if($count100==100){last toploop}
		};
	
	$count100=0;
printloop: while ($count100<100){
    $count100++;
    $direc=$entrydata{$count100}{direc};
    $change=$entrydata{$count100}{change};
    $count=$entrydata{$count100}{count};
    $key=$entrydata{$count100}{key};
    $title=$entrydata{$count100}{title};
    print OUTPUT <<EOF;
<TR VALIGN=MIDDLE CLASS=clis><TD><FONT SIZE=2>$count100</FONT></TD><TD><FONT SIZE=1>$direc$change</FONT></TD><TD><FONT SIZE=2>$count</FONT></TD><TD><A HREF=\"..$key\">$key</A></TD><TD><FONT SIZE=2>$title</FONT></TD></TR>
EOF
print NT100 "$count100:$key\n";
    $total100+=$count;
    if($count100==100){last printloop}
};
	print OUTPUT <<EOF;
</TABLE>
Total hits last month on top 100 = $total100 (out of $total over $pagecount pages at RBJones.com)
<HR WIDTH="70%">
</CENTER>
</BODY>
</HTML>
EOF
	close OUTPUT;
	close NT100;
	$total
};

sub gettitle
{my($ifilename)=@_;
 my($title)="";
#print $ifilename;
 if (-f $ifilename)
 { open (INFILE, "$ifilename") || die "failed to open file $ifilename";
   while (<INFILE>)
   {if (/<[Tt][Ii][Tt][Ll][Ee]>(.*)$/)
      { $title="";
        $_=$1;
#	print;
        do  
        { if (/([^<]*)<\/[Tt][Ii][Tt][Ll][Ee]>/)
            { $title=$title.$1;
#	      print "gettitle:$1\n";
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
 $title
};

1;
