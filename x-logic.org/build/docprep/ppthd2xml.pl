#!/usr/bin/perl -w
# for translating a ProofPower theory listing into X(HT)ML
# Does not eliminate special characters.

# parameters:
# 1. input file (theory listing)
# 2. output file root
# 5. path to root directory

use XLogic::xpptran;

#$true=1;
#$false=0;

$filebase = $ARGV[0];
#print "filebase:$filebase\n";
$webroot = $ARGV[1];

$xml=".xml";

$top="$filebase$xml";

&ppholth2xml($top, $filebase, $webroot);

sub ppholth2xml {
#requires the following parameters:
#1-3. $top, $index, $main - three filenames for output files (base only)
#4. $webroot - path to root directory
	my($top, $filebase, $webroot)=@_;
# the following association list is used for passing information
# to the xml generation package:
	my(%info)=();
	my $mainh;
	$info{"mainn"}=$top;
	$info{"name"}=$filebase;
	$info{"root"}=$webroot;
#	$info{"rbjpub"}=$rbjpub;
# the following local variables are set from the input file
# once: $banner
	my($banner)="No banner";
# once per section: $section
	my($section)="unknown section";
	local *IN;
	open (*IN, "$filebase.thd") || die "failed to open file $filebase.thd";
	$info{"inh"}=*IN;
#	open (TOP, "> $top$xml") || die "failed to create file $top$xml";
#	open (INDEX, "> $index$xml") || die "failed to create file $index$xml";
#	open (MAIN, "> $main$xml") || die "failed to create file $main$xml";
	$info{"mainh"}=MAIN;
	$_=<IN>;
L:	while ($_) {
#	print;
		if (/^\s*$/) {next L};
		if (/^=THEORYLISTINGBANNER/) {
			$_=<IN>;
			chomp;
			$banner=$_;
			$info{"title"}=$banner;
			$info{"title"}=~s/THE THEORY\s+(.*)/The Theory $1/;
			$theoryname=$1;
			$info{"description"}="A complete listing of the theory $theoryname.";
			$info{"keywords"}="ProofPower TheorY FactasiA $theoryname";
#			print "name:".$info{"name"}."\n";
			%info=&openim(%info);
			$mainh=$info{"mainh"};
			die "main file handle not defined\n" unless defined $mainh; 
			$_=<IN>}
		elsif (/^=THEORYLISTINGSECTION/) {
			$_=<IN>;
			chomp;
			s/ /\_/g; $section=$_;
#			print "section: $section\n";
			$info{"section"}=$section;
			&nextsection(%info);
#			print MAIN "<A NAME=\"$section\">$section</A>\n";
			$_=<IN>}
		elsif (/^=THEORYLISTINGTABLE/) {&tran_tlt(%info)}
		elsif (/^=THEORYLISTINGOTHER/) {&tran_tlo(%info)}
		elsif (/^=THEORYLISTINGTRAILER/) {&closeim(%info);$_=""}
		elsif (/^=TEX/) {
			$_=<IN>;
			if (/^=/) {next L};
			print $mainh "<ft lang=\"xl-tex\">\n";
			while(!/=/) {
				$_=&XLogic::xpptran::tranppdoc2xml($_);
				print $mainh "$_<ftbr />";
				$_=<IN>};
			print $mainh "<\/ft>\n<\/section>\n";
			next L;
		}
		else {die "\nUnable to comprehend line: \"$_\"\n"}
	}
};

# Open the output file and write to the point where the sections begin.

sub openim {
	my(%info)=@_;
	my($title,$mainn,$name,$description,$keywords,$root,$up);
	local *MAIN;
	$title=$info{"title"};
	unless (defined($title)) {$title= "untitled index"};
	$mainn=$info{"mainn"};
	unless (defined($mainn)) {die "no main filename\n"};
	$name=$info{"name"};
	unless (defined($name)) {die "no filename base\n"};
	$description=$info{"description"};
	unless (defined($description)) {$description="A full listing of the ProofPower theory $name"};
	$keywords=$info{"keywords"};
	unless (defined($keywords)) {$keywords="ProofPower Formal Theory $name"};
	$root=$info{"root"};
	unless (defined($root)) {die "no root path\n"};
	$up=$info{"up"};
	unless (defined($up)) {$up= "index.html"};
	open (*MAIN, "> $mainn") || die "failed to create file $mainn\n";
	$info{"mainh"}=*MAIN;
	print MAIN <<End;
<?xml version="1.0"?>
<!DOCTYPE ProofPower SYSTEM "pp-symbol.ent">
<xldoc xmlns="http://www.x-logic.org/xmlns/draft/xld"
       xmlns:xhtml="http://www.w3.org/TR/xhtml1/strict"
       name="$name"
       title="$title"
       description="$description"
       keywords="$keywords"
       class="con"
       root="$root"
       up="$up"
       maintitle="mnt">
End
	%info;
};

# section start tag

sub nextsection {
	my(%info)=@_;
	my($mainh,$mainn,$section);
	$mainh=$info{"mainh"};
	unless (defined($mainh)) {die "no main filehandle\n"};
	$section=$info{"section"};
	unless (defined($section)) {die "no section name\n"};
	print $mainh <<End;
<section title="$section">
End
};

# Transcribe a THEORYLISTINGTABLE

sub tran_tlt {
	my(%info)=@_;
	my($inh, $mainh);
	$inh=$info{"inh"};
	unless (defined($inh)) {die "no input filehandle\n"};
	$mainh=$info{"mainh"};
	unless (defined($mainh)) {die "no main filehandle\n"};
	$_=<$inh>;
	print $mainh "<pptlt>\n<col>";
	while (!/^=/) {
		$_=&XLogic::xpptran::tranppdoc2xml($_);
		s/&lib;//g; s/&rib;//g;
		s/\t/<\/col><col>/g; s/\n/<ftbr \/><\/col>\n<col>/g;
		print $mainh $_;
		$_=<$inh>
		};
	print $mainh "</col></pptlt>\n</section>\n"
};


# Transcribe a THEORYLISTINGOTHER

sub tran_tlo {
	my(%info)=@_;
	my($inh,$mainh,$open,$rbjpub);
	$inh=$info{"inh"};
	unless (defined($inh)) {die "no input filehandle\n"};
	$mainh=$info{"mainh"};
	unless (defined($mainh)) {die "no main filehandle\n"};
	$_=<$inh>;
	print $mainh "<pptlo>\n";
	$open=0;
	while (!/^=/) {
		$_=&XLogic::xpptran::tranppdoc2xml($_);
		s/&lib;//g; s/&rib;//g;
# and the &, < and > chars
#		s/&/&amp;/g;
#		s/</&lt;/g;
#		s/>/&gt;/g;
#		s/\333//g; s/\335//g;
		if (/^([^\t]+)\t(.*)$/) {
			if ($open == 1) {$_ = "<name>$1</name><value>$2"}
			elsif ($open == 2) {$_ = "\n</value></entry>\n<entry><name>$1</name><value>$2"}
			else {$_ = "<entry><name>$1<\/name><value>$2"};
			$open=2;
		}
		elsif (/^([^\t]+)$/) {
			if ($open == 1) {$_ = "<name>$1<\/name>\n"}
			elsif ($open == 2) {$_ = "<\/value><\/entry>\n<entry><name>$1<\/name>"}
			else {$_ = "<entry><name>$1<\/name>"};
			$open=1;
		}
		elsif (/^\t(\s*)(.*)$/) {
			my $indent = length($1)*9; my $fill="";
			if ($indent) {$fill="<img name=\"fill.gif\" width=\"$indent\" height=\"1\" \ alt=\"fill\"/>"};
			if ($open == 2) {$_ = "<ftbr \/>\n$fill$2"}
			elsif ($open == 1) {$_ = "<value>$fill$2\n"}
			else {$_ = "<entry><value>$fill$2\n"};
			$open=2;
		}
		else {print "No Match: $_"};
		print $mainh $_;
		$_=<$inh>
		};
	if ($open == 1) {print $mainh "<\/entry>\n"}
	elsif ($open == 2) {print $mainh "<\/value><\/entry>\n"};
	$open=0;
	print $mainh "<\/pptlo>\n</section>\n"
};

# Write the endings to the index and main files

sub closeim {
	my(%info)=@_;
	my($mainh,$rbjpub);
	$mainh=$info{"mainh"};
	unless (defined($mainh)) {die "no main filehandle\n"};
	print $mainh <<End;
</xldoc>
End
	close $mainh;
};




