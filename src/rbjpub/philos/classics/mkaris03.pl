$modified="96/11/30";
$created="96/11/25";

#sub readparams
#{	$parafile=$_[0];
#	open (PARAMETERS, $parafile);
#	while(<PARAMETERS> && /(\a+):(.*)$/){$($1)=$2};
#};

# The controldata file consists of the following kinds of records:
# File:filenumber:filename:filetype(single book=SB multiple book-MB):filetitle
# Book:booknumber:booktitle
# Part:partnumber:parttitle
# Para:paranumber:paratitle
# THEY MUST BE in ascending order

# When it is read in a data structure is created which is a direct representation
# of its content.
# controldata{"filecount"}=number of files
# controldata{n}=file information (file n)
# controldata{n}{"name"}=filename
# controldata{n}{"title"}=filetitle
# controldata{n}{"type"}=filetype
# controldata{n}{"numbooks"}=number of books in the file
# controldata{n}{m}=book information (file n book m)
# controldata{n}{m}{"title"}=title for file n book m
# controldata{n}{m}{o}{"title"}=title for file n book m part o
# controldata{n}{m}{o}{p}{"title"}=title for file n book m part o para p

sub readcontroldata
{	my($controlfile)=$_[0];
	my(%control) = ();
	my($file, $book, $part, $para)= (0,0,0,0);
	open (CONTROL, $controlfile) || die "can't open control file: $controlfile \n";
	loop: for (<CONTROL>)
	{if (/File:(\d+):([^:]*):([^:]*):([^:]*):(.*)$/)
		{	$control{$1} = {"name"=>$2,
					"type"=>$3,
					"numBooks"=>$4,
					"title"=>$5};
			$control{"filecount"}=$1;
			$file=$1;
			next loop
		};
	if (/Book:(\d+):(.*)$/)
		{	$control{$file}{$1}={"title"=>$2};
			$book=$1;
			next loop
		};
	if (/Part:(\d+):(.*)$/)
		{	$control{$file}{$book}{$1}={"title"=>$2};
			$part=$1;
			next loop
		};
	if (/Para:(\d+):(.*)$/)
		{	$control{$file}{$book}{$para}{$1}={"title"=>$2};
			$para=$1;
			next loop
		};
	};
	close CONTROL;
	\%control
};

sub strip
{     $_[0] =~ s/^\s*\b(.*)\b\s*$/$1/; $_[0];
};

sub parano
{	s/(^\s*)(\d*)(\.)(.*)$/$1$4/;
	$2;
};

sub paraTitle
{	$paraTitle="";
	while (/^([^.\?:;]+)$/) {$temp=$1; chop $temp; $paraTitle.=" $temp"; &readLine;};
	if (s/^([^.\?:;]*[.\?:;]\s*)(.*)$/$2/) {$temp=$1; chop($temp); $paraTitle.=" $temp";};
	if ($trace>4) { print "paraTitle: $paraTitle\n";
			print "rest: $_\n"
			};
#	chop;
#	while ((/^\s*$/) && !eof(<INPUT>)) {&readLine; chop;};
};

sub openFile
{	my($filename)=$_[0];
	open (INPUT,$filename) || die "unable to open file $filename";
	$_=<INPUT>;
	while (/^\s*$/) {$_=<INPUT>};
	$sourceDate=&strip($_);
	$_=<INPUT>;
	$sourceTitle=&strip($_);
	$_=<INPUT>;
	$sourceAuthor=&strip($_);
	$_=<INPUT>;
	$sourceTranslator=&strip($_);
	$_=<INPUT>
};

sub closeFile
{	close INPUT
};

sub readLine
{	if (!eof(INPUT)) {$_=<INPUT>} else {$_=""};
};

sub testBookStart
{	if (/^\s*Book\s*(\w+)\s*$/)
	{	if ($trace>2) {print "book $book\n"};
		1
	} else {0}
};

sub testSBPartStart
{#	print "testSBPartStart";
	if (/^\s*Part\s*(\w+)\s*$/)
	{	if ($trace>2) {print "Part $part\n"};
		$partHead="Part $1";
		1
	} else {0}
};

sub testMBPartStart
{#	print "testMBPartStart";
	if (/^\s*(\d+)\s*$/)
	{	if ($trace>2) {print "part $part\n"};
		$partHead=$1;
		1
	} else {0}
};

1;
