# $Id: btxt2txt.pl,v 1.2 2012/06/05 20:09:55 rbj Exp $

$file=$ARGV[0];

if (-r "$file.btxt"){open (INPUT, "$file.btxt");}
else {die "File $file.txt not readable\n";};
#if (-e "$file.doc"){die "File $file.doc already exists\n";}
#else {open (OUTPUT, "> $file.doc");};
open (OUTPUT, "> $file.txt");

$_=<INPUT>;
while ($_)
{&nextstructure;};
&windup;
exit;

sub nextstructure
{
 {print OUTPUT;};
if (eof(INPUT)) {$_="";} else {$_=<INPUT>; &translate;};};

sub translate
{
	s/\200/\\[AN]/g;
	s/\201/\\[OR]/g;
	s/\202/\\[hA]/g;
	s/\203/\\[fa]/g;
	s/\204/\\[te]/g;
	s/\205/|\\h'-10M'-\\h'-10M'-/g;                 # turnstile
	s/\206/\\zN\\h'3M'N/g;
	s/\207/\\[*m]/g;
	s/\210/\\[!=]/g;
	s/\211/\\[mu]/g;
	s/\212/\\[rA]/g;
	s/\213/\\[->]/g;                                # total function space
	s/\214/\\[no]/g;
	s/\215/\\[*l]/g;
	s/\216/\\[bu]/g;
	s/\220/\\[<>]/g;
	s/\221/\\v'1M'\\[*I]\\v'-1M'\\h'-18M'\\[*R]/g;  # power set
	s/\223/\\[nm]/g;
	s/\224/=/g;
	s/\225/\\[c+]/g;
	s/\226/\\o'\\[->]\\s-4\\v'-8M'|\\v'8M'\\s+4'/g; # partial function
	s/\227/\\s-5\\[ba]\\h'-10M'\\[->]\\s+5/g;       # maplet
	s/\235/\\[mo]/g;
	s/\240/\\[ca]/g;
	s/\241/\\[cu]/g;
	s/\242/\\s+3\\[ca]\\s-3/g;                      # distributed intersection 
	s/\243/\\s+3\\[cu]\\s-3/g;                      # distributed union
	s/\244/\\[es]/g;
	s/\245/\\[ib]/g;
	s/\254/\\[S2]/g;
	s/\255/\\[*H] /g;
	s/\260/\\[S1]/g;
	s/\262/\\d\\s-4f\\s+4\\u/g;                     # subscript f
	s/\264/\\[pp]/g;
	s/\266/==/g;
	s/\272/:/g;
	s/\276/</g;
	s/\277/>/g;
	s/\300/\\[te]\\d\\s-61\\s+6\\u/g;               # 
        s/\307/.sd /g;
        s/\310/.sv /g;
        s/\311/.sb /g;
        s/\312/.se /g;
        s/\313/.sw /g;
        s/\315//g;
	s/\323/\\[sc]/g;
	s/\324/\\v'20M'\\s-3p\\s+3\\v'-20M'/g;
	s/\325/\\v'20M'\\s-3s\\s+3\\v'-20M'/g;
	s/\326/\\v'20M'\\s-3z\\s+3\\v'-20M'/g;
	s/\335//g;
	s/\337//g;
	s/\340//g;
	s/\341//g;
	s/\342//g;
	s/\345/.hd /g;
	s/\346/.he /g;
	s/\347/.sv /g;
	s/\364/\\[*b]/g;
	s/\365/\\[*f]/g;
	s/\366/\\[*G]/g;
	s/\367/\\[*L]/g;
	s/\370/\\[*l]/g;
	s/\372/\\[*P]/g;
	s/\375/\\[*W]/g;
	s/\376/\\[*m]/g;
	s/\377/\\z\\[*N]\\h'10M'\\[*N]/g;

};

sub windup
{
	print OUTPUT <<END;
END
};
