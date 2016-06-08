#!/usr/local/bin/perl -w
# $Id: cleanfiles.pl,v 1.1.1.1 2006-04-19 20:44:51 rbj01 Exp $
# PERL script for cleaning text files after tranfer between Linux
# and windows.
# This is needed because I access CVS from Windows but all development
# is done under Linux.  Linux is willing to attempt the conversion
# but has no good way of recognising which files are tex files.
# This script should work in both directions.

$basedir_old=$ARGV[0];
&scandirs($basedir_old,"",\&clean_txt);

# The following subroutine walks a cvs directory tree listing each
# directory and feeding the results to a procedures passed to it 
# as its third parameter.

sub scandirs {
	my ($basedir,$reldir,$proc)=@_;
	my $dir="$basedir$reldir";
	my (@dircon, $filepath);
	opendir (DIR, $dir) || die "Failed to open directory $dir";
	@dircon=readdir(DIR);
	closedir DIR;
	foreach $filename (@dircon) {
		if ($filename eq "." || $filename eq "..") {next};
		$filepath="$dir/$filename";
		if (-d $filepath) {&scandirs($basedir,"$reldir/$filename",$proc);};
	};
	&$proc($basedir,$reldir,\@dircon);
};

# the following procedure copies each file to normalised the newlines.

sub clean_txt {
	my ($basedir, $reldir, $names)=@_;
	my $dir = "$basedir$reldir";
	my ($file,$move,$count);
	my $tempfile =  "/tmp/cleanfiles$$";
	foreach $name (@$names) {
		$file = "$dir/$name";
		if (-d $file or $file=~/.*(\.)gif$/) {next};
#		print "Cleaning $file, temp=$tempfile\n";
		open (OF, "> $tempfile") || die "Unable to create $tempfile";
		open (IF, $file) || die "Unable to open $file";
		while (!eof (IF)) {
			$_=<IF>; chomp;
			s/\r//g;
			print OF "$_\n";
			};
		close IF; close OF;
		my $move ="mv $tempfile $file";
		system ($move);
	};
};
