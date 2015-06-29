# $Id $
$created="25/7/95";
$updated="26/7/95";
$file=$ARGV[0];

sub translate
{	s/\\fI/<EM>/g;
	s/\\fP/<\/EM>/g;
	s/\\\*d/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/or\.gif\" ALT=and BORDER=0>/g;
	s/\\\*o/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/turnstil\.gif\" ALT=turnstil BORDER=0>/g;
	s/\\\(\*i/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/iota\.gif\" ALT=iota BORDER=0>/g;
	s/\\\(\*l/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/lambda\.gif\" ALT=lambda BORDER=0>/g;
	s/\\\(\*C/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/cchi\.gif\" ALT=cchi BORDER=0>/g;
	s/\\\(\*D/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/cdelta\.gif\" ALT=cdelta BORDER=0>/g;
	s/\\\(\*F/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/ctor\.gif\" ALT=ctor BORDER=0>/g;
	s/\\\(\*G/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/cpi\.gif\" ALT=cpi BORDER=0>/g;
	s/\\\(\*H/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/cpsi\.gif\" ALT=cpsi BORDER=0>/g;
	s/\\\(ib/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/subsetof\.gif\" ALT=subsetof BORDER=0>/g;
	s/\\\(cu/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/scup\.gif\" ALT=scup BORDER=0>/g;
	s/\\\(ca/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/scap\.gif\" ALT=scap BORDER=0>/g;
	s/\\\(no/<IMG SRC=\"\.\.\/\.\.\/\.\.\/rbjgifs\/not\.gif\" ALT=not BORDER=0>/g;
};
