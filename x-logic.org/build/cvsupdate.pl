#!/usr/local/bin/perl -w
# $Id: cvsupdate.pl,v 1.1.1.1 2006-04-19 20:44:51 rbj01 Exp $
# PERL script for updating the Sourceforge CVS repository from Windows
# after the checked out source has been copied to Linux, amended and
# then copied back to Windows.
# (this is for OpenSource workers who have a box with a WinModem)
# The problem is that the copying, which is essential for the script
# to work (since it changes the text files from Windows to Unix formats)
# also messes about with the case of the file and directory names,
# and doesn't reverse the changes when you copy back (but makes more)
# and this all varies according to which version of Linux you are running.
# (These are copies to and from a DOS partition mounted under Linux.)

# The main thing that the script must do is sort out the case of the
# files.  But since I can't do cvs add while I am working it would
# be nice if the script sorted that out.  And if its doing that it
# just as well do the cvs update and commit as well.

# Some assumptions are necessary in order to be able to do this.
# These are the assumptions I make:
# 1.  In no directory will there be two files or directories whose
#     Names differ only in case.
# 2.  Most filenames and directory names are in lower case.
# 3.  "CVS" is only used for cvs directories, and therefore should
#     always be in upper case.

# There will be two modes of operation:
# 1. Non-interactive, in which new files and directories are
#    normalised to lower case and automatically "added".
# 2. Interactive, in which new files are only added after
#    a dialogue in which the user may change their case or
#    chose not to add them at all.

# In order to do its job the script must have access to two copies
# of the cvs repository.  The before and after repositories.
# There will be two scans:
# 1. To identify any names in the new version which occur in the
#    same directory with multiple case variants.
#    Any found are reported and the script aborts.
# 2. To make any necessary case alterations and to delete any
#    new files which the user may chose not to add.
#    Files of cvs commands are generated.
# -drbjones@cvs.x-logic.sourceforge.net:/cvsroot/x-logic 

#$scriptdir=$ARGV[0];
#$basedir_old=$ARGV[1];
#$basedir_new=$ARGV[2];
$scriptdir="/dosb/xfer/cvsud";
$basedir_old="/home/rbj/x-logic.old";
$basedir_new="/home/rbj/x-logic";

#$basedir_old=~s/\//\\/g;
#$basedir_new=~s/\//\\/g;

open (CVS, "> $scriptdir/cvs") || die "unable to create file $scriptdir/cvs";
open (REN, "> $scriptdir/ren") || die "unable to create file $scriptdir/ren";

$clash=0;
&scandirs($basedir_old,"",\&list_clashes);
if ($clash) {die "Run terminated, $clash clashes on $basedir_old."};
$clash=0;
&scandirs($basedir_new,"",\&list_clashes);
if ($clash) {die "Run terminated, $clash clashes on $basedir_new."};

&scandirs($basedir_new,"",\&compdirs);

print CVS <<EOF;
cvs commit
EOF

# The following procedure takes a list of filenames and checks
# whether there are any duplicates (on case insensitive comparison). 
# It returns a reference to a list of pairs of clashing names. 

sub list_clashes {
	my ($basedir, $reldir, $names)=@_;
	my %clashes=();
	my %namehash=();
	my $other;
	foreach $name (@$names) {
		my $lcname=lc($name);
		if (exists $namehash{$lcname}) {
			$clash++;
			$other=$namehash{$lcname};
		    if (exists $clashes{$lcname}) {$clashes{$lcname}.=", $name"}
			else {$clashes{$name}="$name, $other"};
		}
		else {$namehash{$lcname}=$name};
	};
	if (%clashes) {
		print "Clashes in directory $basedir/$reldir:\n";
		foreach $key (keys(%clashes)) {my $other=$clashes{$key}; print "\t$other\n";};
	};
	return 0;
};

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

# The following procedure accepts a listing of a directory in the new cvs
# and checks it out against the old cvs.

sub compdirs {
	my ($basedir, $reldir, $names)=@_;
	my $dir = "$basedir_old$reldir";
	my (@dircon, %new2old, %old2new, %add, %remove) = ((),(),(),());
	my ($lcfn,$lcofn);
	opendir (DIR, $dir) || die "Failed to open directory $dir";
	@dircon=readdir(DIR);
	closedir DIR;
	foreach $filename (@$names) {
#		if ($filename eq "." || $filename eq ".."){next};
		$lcfn = lc($filename);
		foreach $oldfn (@dircon) {
			if (lc($oldfn) eq $lcfn) {
				$new2old{$filename}=$oldfn;
				if (!($oldfn eq $filename)) {
					print REN <<EOF;
mv $basedir$reldir/$filename temp
mv temp $basedir$reldir/$oldfn
EOF
				};
				$old2new{$oldfn}=$filename;
#				print "!O:$oldfn:N:$filename";
				last;
			};
		};
		if (!defined($new2old{$filename})) {
			$add{$filename}=$lcfn;
			if (!(($filename eq $lcfn) || ($filename="README"))) {
				print REN <<EOF;
mv $basedir$reldir/$filename temp
mv temp $basedir$reldir/$lcfn
EOF
			};
#			$_="$reldir";
#			s/\//\\/g;
#			$dosdir=$_;
			print CVS <<EOF;
pushd .$reldir
cvs add $lcfn
popd
EOF
			};
	};
  l1:	foreach $oldfn (@dircon) {
	  if (!defined($old2new{$oldfn})) {
		  	print CVS <<EOF;
pushd .$reldir
cvs delete $oldfn
popd
EOF
			$remove{$oldfn}=1;
	  };
  };
};






