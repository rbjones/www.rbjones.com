#!/usr/bin/perl -w
# ($Id)

# This file creates an index by scanning a tex file.

# The tex file is taken from STDIN the results sent to STDOUT.

%iwords=();
$maxcount=0;

while (<STDIN>) {
    my $line=$_;
    my $name;
    while ($line=~s/([\w]+(-[\w]+)*)//) {
	$name=lc($1);
	if (defined ($iwords{$name})) {
	    $newcount=($iwords{$name}+=1);
	    if ($maxcount<$newcount){$maxcount=$newcount}}
	else {$iwords{$name}=1}
    }
};

my @Buf=();

foreach $word (keys %iwords) {$line=sprintf("\t%-40s %06d", $word, $iwords{$word}); push (@Buf, $line)};

my @sBuf= sort @Buf;

foreach $wc (@sBuf) {print "$wc\n"};
