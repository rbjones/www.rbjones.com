#!/usr/bin/perl -w

use HTML::Parser ();
use Data::Dump ();

print "START\n\n";

@stack=();
print "Empty stack length:".$#stack."\n";
$topitem=[];
$previtem=[];

@atomic_tags=qw(dt dd img li link p br hr);

sub start {
    my($attr,$tagname)=@_;
    $topitem={atag=>$tagname, attr=>$attr, content=>[]};
#    print "\n\nSTARTTOPITEM=";
#    print Data::Dump::dump($topitem);
#    print "\n\n-----sti------\n\n";
    push(@stack, $topitem)
};

sub end {
    $topitem=pop(@stack);
#    print "\n\nENDTOPITEM1=";
#    print Data::Dump::dump($topitem);
#    print "\n\n-----eti1------\n\n";
    $previtem=$stack[$#stack];
    $content=${$previtem}{content};
    push(@{$content}, $topitem);
#    print "\n\nENDTOPITEM2=";
#    print Data::Dump::dump($previtem);
#    print "\n\n-----eti2------\n\n";
    $topitem=$previtem
};

sub h {
    my($event, $line, $column, $text, $tagname, $attr) = @_;
    if ($event eq "start_document") {
	$topitem={atag=>"doc", attr=>{}, content=>[]};
	push(@stack, $topitem);
    }
    elsif ($event eq "start") {
	if (substr($tagname,-1) eq '/'){
	    $tagname=substr($tagname,0,length($tagname)-1);
	    &start($attr,$tagname);
	    &end()
	}
	else {
	    &start($attr,$tagname);
	    foreach $at (@atomic_tags) {
		if ($at eq $tagname) {&end}
	    };
	};
    }
    elsif ($event eq "end") {&end}
    elsif ($event eq "text") {
	my $stacksize= $#stack;
#	print "stacksize:$stacksize:$text\n\n";
	if ($stacksize>=0) {
	    $content=${$stack[$stacksize]}{content};
	    push(@{$content}, {text=>$text});
 #   print "\n\nTEXT=";
 #   print Data::Dump::dump($stack[$stacksize]);
 #   print "\n\n-----text------\n\n";
	};
    };
}

my $p = HTML::Parser->new(api_version => 3);

$p->handler(default => \&h, "event, line, column, text, tagname, attr");
$p->parse_file(@ARGV ? shift : *STDIN);

print Data::Dump::dump(@stack), "\n";

print "Stack length:".$#stack."\n";
