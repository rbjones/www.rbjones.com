# PERL script to create glossary index
$created="1999/9/18";
$modified="2015-06-27";

$base=$ARGV[0]."/rbjpub/philos/glossary";
$category=$ARGV[1];
#this is the category of entry to select for inclusion in this list
$file=$ARGV[2];
if (defined($ARGV[3])) {$classsuffix=$ARGV[3]}
	else {$classsuffix=""};

print "mkglist: \$category=$category; \$file=$file; \$classsuffix=$classsuffix\n";

#this is the filename to receive the list
$gifdir="../../../rbjgifs";
$listf="$base/$file"."2.htm";

#print "category = $category; ";
#print "base = $base; ";
#print "listf = $listf\n";

#$_=<STDIN>;

open (LIST,"> $listf") or die "unable to open output list";

print LIST <<END;
<HEAD>
<LINK REL=STYLESHEET TYPE="text/css" HREF="../../prof/p1sty.txt" TITLE="Resource">
<TITLE>MainFrame: words about $category</TITLE>
<META name="description"
content="glossary of $category words">
<META name="keywords" content="RbJ InterneT $category WorD GlossarY">
</HEAD>
<BODY CLASS=re2>
<B>
END

foreach ($letter="a"; $letter ne "aa"; $letter++)
{	$file="$base/$letter.htm";
	$uletter="\U$letter";
#	print "\n$file\n";

  $tag="notag";
  $name="noname";
if (open (INFILE, "< $file"))
{ print LIST <<END;
<A NAME="$uletter"> </A>
<A CLASS=glohead$classsuffix TARGET="_top" HREF="$letter.htm">..$uletter..</A><BR>
<P CLASS=glolist$classsuffix>
END

  $_=<INFILE>;

  while ($_)
  {	if (/<A\s+NAME=\"([^"]*)\">/)
	{	$tag=$1;
#		print "tag=$tag; ";
		$_=<INFILE>;
		while(/<A\s+NAME=\"([^"]*)\">/){$_=<INFILE>};
	};
	if (/<EM\s+CLASS=glotitle\s+(TITLE|Title)=\"([^"]*)\">([^<]*)<\/EM>/)
	{	$name=$3; $cats=$1;
#		print "name = $name; ";
		if ($cats =~ /$category/ || $category eq "")
 		{
#			print "name = $name; cats= $cats;\n";
			print LIST <<END
<A TARGET="_top" HREF="$letter.htm#$tag" CLASS=glolist$classsuffix TITLE="$cats">$name</A><BR>
END
		}
	}
	elsif (/<EM\s+CLASS=glotitle\s*>([^<]*)<\/EM>/)
	{	$name=$1; $cats="";
#		print "name = $name; cats= $cats; ";
		if ($cats =~ /$category/ || $category eq "")
 		{	
#			print "name = $name; cats= $cats;\n";
			print LIST <<END
<A TARGET="_top" HREF="$letter.htm#$tag" CLASS=glolist$classsuffix>$name</A><BR>
END
		}
	}
	elsif (/<A\s+HREF\s*=\s*"[^"]*"\s*CLASS=glotitle\s+(TITLE|Title)=\"([^"]*)\"[^>]*>([^<]*)<\/A>/)
	{	$name=$3; $cats=$1;
#		print "name = $name; cats= $cats; ";
		if ($cats =~ /$category/ || $category eq "")
 		{	
#			print "name = $name; cats= $cats;\n";
			print LIST <<END
<A TARGET="_top" HREF="$letter.htm#$tag" CLASS=glolist$classsuffix>$name</A><BR>
END
		}
	}
	elsif (/<A\s+HREF\s*=\s*"[^"]*"\s*CLASS=glotitle\s*>([^<]*)<\/A>/)
	{	$name=$1; $cats="";
#		print "name = $name; cats= $cats; ";
		if ($cats =~ /$category/ || $category eq "")
 		{	
#			print "name = $name; cats= $cats;\n";
			print LIST <<END
<A TARGET="_top" HREF="$letter.htm#$tag" CLASS=glolist$classsuffix>$name</A><BR>
END
		}
	};
	$_=<INFILE>;
   };
 };

print LIST <<END;
</P>
END
close INFILE;
};
print LIST <<END;
</B>
</TH></TR></TABLE>
<P>
<CENTER>
<HR WIDTH="70%">
<A TARGET="_top" HREF="index.htm"><IMG SRC="$gifdir/up.gif" ALT="UP" BORDER=0></A>
<A TARGET="_top" HREF="../../index.htm"><IMG SRC="$gifdir/home.gif" ALT="HOME" BORDER=0></A>
&copy; <A TARGET="_top" HREF="../../rbj.htm"><IMG SRC="$gifdir/rbjin1.gif" ALT="RBJ" ALIGN=absmiddle BORDER=0></A><BR>
created $created<BR>
modified $modified
</CENTER></BODY>
END

close LIST;

