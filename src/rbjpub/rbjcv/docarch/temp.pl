# $Id: temp.pl,v 1.1 2012/06/29 21:42:53 rbj Exp $

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
	s/\356/\.\./g;
	s/\345/=SML/g;
	s/\346/=TEX/g;
	s/\363/=IGN/g;
	s/\350/\001/g;
	s/\352/\002/g;
	$a= "\200\201\202\203\204\205\206\211\212\213\214\216\220\221\225\226\227"
	    ."\232\233\235\236\237\273\274\276\277\311\312\313\315\335\337"
	    ."\340\341\342\351\353\361";
	$b= "\261\262\244\265\266\364\356\270\264\255\263\267\252\360\253\337\355"
	    ."\362\341\215\274\276\361\256\247\242\367\210\260\374\334\374"
	    ."\374\335\333\377\235\204";
	eval "tr/$a/$b/";
	s/\001/\271Z/g;
	s/\002/\271ZAX/g;
	s/\310/\271HOLCONST/g

#	print "$_\n";
};

sub translate3
{
#       print "$_\n";
	s/\356/\.\./g;
	s/\345/=SML/g;
	s/\346/=TEX/g;
	s/\363/=GFT /g;
	s/\350/\001/g;
	s/\352/\002/g;
    tr/\200\201\202\203\204\205\206\212\213\214\216\220\221\225\226\227\232\233\235\236\237\273\274\276\277\311\312\313\315\335\337\340\341\342\351\353\361/\261\262\244\265\266\364\356\264\255\263\267\252\360\253\337\355\362\341\215\274\276\361\256\247\242\367\210\260\374\334\374\374\335\333\377\235\204/;
	s/\001/\271Z/g;
	s/\002/\271ZAX/g;

#	print "$_\n";
};


sub windup
{
	print OUTPUT <<END;
END
};
