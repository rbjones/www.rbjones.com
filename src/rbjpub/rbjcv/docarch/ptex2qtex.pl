# $Id: ptex2qtex.pl,v 1.2 2010/02/10 11:17:12 rbj Exp $

$file=$ARGV[0];

if (-r "$file.ptex"){open (INPUT, "$file.ptex");}
else {die "File $file.ptex not readable\n";};
#if (-e "$file.doc"){die "File $file.doc already exists\n";}
#else {open (OUTPUT, "> $file.doc");};
open (OUTPUT, "> $file.qtex");

$_=<INPUT>;
while ($_)
{&nextstructure;};
&windup;
exit;

sub nextline
{if (eof(INPUT)) {$_="";} else {$_=<INPUT>; &translate2;};};

sub proctocom
{&nextline;
while ($_ && !(/^$_[0]/)) {&nextstructure;};
};

sub copytodot
{&nextline;
while ($_ && !(/^\./)) {print OUTPUT; &nextline;};
};

sub nextstructure
{
 {print OUTPUT;};
&nextline;};

sub translate2
{
#       print "$_\n";
	s/\345/=SML/g;
	s/\346/=TEX/g;
	s/\313/\260/g;
	s/\350/\271Z/g;
	s/\342/\333/g;
	s/\352/\271ZAX/g;
	s/\220/\252/g;
	s/\351/\377/g;
	s/\335/\334/g;
	s/\341/\335/g;
	s/\315/\374/g;
	s/\337/\374/g;
	s/\340/\374/g;
	s/\311/\367/g;
	s/\312/\210/g;
	s/\203/\265/g;
	s/\216/\267/g;
	s/\200/\261/g;
	s/\212/\264/g;
	s/\276/\247/g;
	s/\277/\242/g;
#	s/\211/\270/g;
	s/\213/\255/g;
	s/\227/\355/g;
	s/\235/\215/g;
	s/\201/\262/g;
	s/\202/\244/g;
	s/\232/\362/g;
	s/\221/\360/g;
	s/\205/\364/g;
	s/\353/\235/g;
#	print "$_\n";
};

sub windup
{
	print OUTPUT <<END;
END
};
