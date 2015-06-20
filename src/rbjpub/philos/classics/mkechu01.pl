#!/usr/local/bin/perl
# called with parameters as follows:
# 1. input filename
# 2. top output filename
# 3. output filestem
# 4. output subdir

$created="1999/12/2";
$modified="1999/12/2";
$infile=$ARGV[0];
$topout=$ARGV[1];
$outstem=$ARGV[2];
$subdir=$ARGV[3];
$suff=".xml";
$wtout=$outstem."iwe".$suff;
$xmlheader="<?xml version=\"1.0\" encoding=\"iso-8859-1\" ?>";
$xmlnamespace="http://www.rbjones.com/xmlns/ns1";
$desctail=" of Hume's Enquiry Concerning Human Understanding.";
$titlestart="Hume's Enquiries: ";
$keywords="PhilosophY HumE";
$rbjpub="../../../";
$class="con";

$secno=0;

open(INPUT,$infile) || die "failed to open file $infile\n";
$_ = <INPUT>;
# open(TOPOUT, "> $subdir/$topout") || die "failed to create file $topout\n";
&wiretap;
while (!eof(INPUT)){
	&section
	};
close(INPUT);

sub wiretap {
	open(OUTPUT, "> $subdir/$wtout") || die "failed to create file $wtout\n";
	$outfilestem=$outstem."iwe";
	$outfilename=$outfilestem.".htm";
	$title="Wiretap info";
        $description="About the Wiretap online edition";
	open (OUTPUT, "> $subdir/$outfilestem.xml") || die "failed to create file $outfilename\n";
	print "OPENED: $subdir/$outfilestem.xml\n";
	print OUTPUT <<OutEnd;
$xmlheader
<ns1:part xmlns:ns1="$xmlnamespace"
	file="$subdir/$outfilename"
	title="$title"
        heading="$title"
	description="$description"
        rbjpub="$rbjpub"
        class="$class">
<center>
<p>
OutEnd
	while (/^(\s|$)/) {
		if (/^\s*$/) {print OUTPUT "</p><p>\n"}
		else {chomp; s/&/&amp;/; s/</&lt;/; s/>/&gt;/;
		      print OUTPUT "$_<br/>\n"};
		$_=<INPUT>
		};
		   print OUTPUT <<OutEnd;
</p>
</center>
OutEnd
		   while(!/^SECTION/) {&para};
	print OUTPUT <<OutEnd;
</ns1:part>
OutEnd
	close OUTPUT
};

sub para{
	print OUTPUT "<p>\n";
	while (!/^\s*$/) {
		while (/^(.*[^-])-\s*$/){
			my $start = $1;
			if (eof(INPUT)){$_=" \n"}
			else {$_=<INPUT>};
			$_=$start.$_
			};
		s/(&)([^a])/&amp;$2/g;
		print OUTPUT;
		$_=<INPUT>
		};
	print OUTPUT "</p>\n";
	while (/^\s*$/){
		if (eof(INPUT)) {return}
		else {$_=<INPUT>};
	}
};

sub section{
	if (/^SECTION\s+(\S*)/){
		$section=$1;
		$secno+=1;
		$partno=0;
		$sectitle=<INPUT>;
		$_=<INPUT>;
		while (/\S/){
			chomp;
			$sectitle.=" $_";
			$_=<INPUT>
			};
		while (/^\s*$/) {$_=<INPUT>};
		while (!(/^SECTION/ || eof(INPUT))) {
			if (/^PART\s+(\S*)/) {
				$part=$1;
				$partno+=1;
				$_=<INPUT>
				}
			else {$part=""};
			&part
			}
		}
	else {die "sub section called but no section\n"}
};

sub part{
	$outfilestem=$outstem.(substr($secno+100,1)).($partno ? $partno : "");
	$outfilename=$outfilestem.$suff;
    $secpart="Section $section".($partno ? " Part $part" : "");
	$title="$titlestart $secpart";
    $description=$secpart.$desctail;
	open (OUTPUT, "> $subdir/$outfilename") || die "failed to create file $outfilename\n";
	$partname = ($part ? "Part $part" : "");
	print OUTPUT <<EndOut;
$xmlheader
<ns1:part xmlns:ns1="$xmlnamespace"
	section="Section $section"
	part="$partname"
	file="$subdir/$outfilestem.htm"
	title="$title"
    heading="$sectitle"
	description="$description"
	keywords="$keywords"
	created="$created"
	modified="$modified"
    rbjpub="$rbjpub"
    class="$class">
EndOut
	while (!(/^(PART|SECTION)/ || (eof(INPUT)))) {
		&para
		};
	print OUTPUT <<EndOut;
</ns1:part>
EndOut
	close OUTPUT
};











