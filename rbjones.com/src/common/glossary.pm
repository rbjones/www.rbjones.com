package glossary;

# 

my $gl="";
my $gs=false;

sub ReadHTMgloss {
    my($infile)=@_;
    open INPUT "<$infile";
    &FindStart($INPUT);
    do {&ReadEntry} until (eof(INPUT)); 
};

sub FindList {
    my($infile)=@_;
    while (<INPUT> && !/<DL>/) {};
    $gl=$_;
    $gl=~s/^[^<]*<DL>//;
    $gs=true;
};

sub ReadList {
    my($infile)=@_;
};

sub FindEntry {
    $gl=$_;
    $gl=~s/^([^<]*<DL>)//;
    if ($gl=~/<\/DL>/) {}
    else {};
};
