# PERL script to create lists of people
$created="1998-12-08";
$modified="2015-06-28";

$base=$ARGV[0]."/rbjpub/philos/bibliog";
#this count determines the filename for this list and the previous one.
#the files included are those which have been modified later than the last list.
$category=$ARGV[1];
#this is the category of person to select for inclusion in this list
$file=$ARGV[2];
if (defined($ARGV[3])) {$classsuffix=$ARGV[3]}
	else {$classsuffix=""};
#this is the filename to receive the list
$gifdir="../../../rbjgifs";
$listf="$base/$file"."2.htm";

#print "category = $category; ";
#print "base = $base; ";
#print "listf = $listf\n";
print "mkplist: \$category=$category; \$file=$file; $classsuffix=$classsuffix; \$base=$base\n";
#$_=<STDIN>;

open (LIST,"> $listf") or die "unable to open output list";

print LIST <<END;
<HEAD>
<LINK REL=STYLESHEET TYPE="text/css" HREF="../../prof/p1sty.txt" TITLE="Resource">
<TITLE>MainFrame: Some $category People and Their Works</TITLE>
<META name="description" content="Links relating to a selection of people who have some interest in $category.">
<META name="keywords" content="RbJ InterneT $category PeoplE">
</HEAD>
<BODY CLASS=re2>
<H2>Some $category People and Their Works</H2>
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
<A CLASS=pephead$classsuffix TARGET="_top" HREF="$letter.htm">..$uletter..</A><BR>
<P CLASS=peplist$classsuffix>
END

  $_=<INFILE>;

  while ($_)
  {	if (/<A\s+NAME=\"([^"]*)\">/)
	{	$tag=$1;
#		print "tag=$tag; ";
		$_=<INFILE>;
		while(/<A\s+NAME=\"([^"]*)\">/){$_=<INFILE>};
	};
	if (/<EM\s+CLASS=author\s+(TITLE|Title)=\"([^"]*)\">([^<]*)<\/EM>/)
	{	$name=$3; $cats=$2;
#		print "name = $name; cats= $cats; ";
		if ($cats =~ /$category/ || $category eq "")
 		{
#			print "name = $name; cats= $cats;\n";
			print LIST <<END
<A TARGET="_top" HREF="$letter.htm#$tag" CLASS=peplist$classsuffix TITLE="$cats">$name</A><BR>
END
		}
	}
	elsif (/<EM\s+CLASS=author[^>]*>([^<]*)<\/EM>/)
	{	$name=$1; $cats="";
#		print "name = $name; cats= $cats; ";
		if ($cats =~ /$category/ || $category eq "")
 		{	
#			print "name = $name; cats= $cats;\n";
			print LIST <<END
<A TARGET="_top" HREF="$letter.htm#$tag" CLASS=peplist$classsuffix>$name</A><BR>
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

