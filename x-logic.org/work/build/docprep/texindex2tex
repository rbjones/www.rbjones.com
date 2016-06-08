#!/usr/bin/perl -w
# for extracting titles and abstracts from a collection of LaTeX
# documents and creating an list of abstracts in XML.

# parameters: input files names
# output to standard output.

# use XLogic::xpptran;

#$true=1;
#$false=0;

$title=""; $abstract=""; $bibref="";

print "\\section{Abstracts}\n";

while (<ARGV>) {
    if (/\\title\{(([^{}]*(\{[^}]*\}))*[^}]*)[^}]*\}/) {$title=$1}
    elsif (/bibref\{([^}]*)\}/) {$bibref=$1}
    elsif (/\\begin\{abstract\}/) {
	$abstract="";
	$_=<ARGV>;
	until (/\\end\{abstract\}/) {s/^\%(.*)$/$1/; $abstract.=$_; $_=<ARGV>};
	print "\\subsection{$title}";
	print "\n\n$abstract";
	if ($bibref) {print "\\cite{$bibref}"};
	print "\n";
        $title=""; $abstract=""; $bibref="";
    };
};
