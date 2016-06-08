#!/usr/local/bin/perl -w
# ($Id)
# Some general purpose routines for use with the XML::DOM

package XLogic::DomXtras;

use XML::DOM;

sub depthMap {
	my ($node, $procedure) = @_;
#	print STDERR "!".sprintf("%d",$node->getNodeType);
	if ($node->getNodeType ==  XML::DOM::ELEMENT_NODE){ 
		my @children = $node->getChildNodes;
#	print STDERR "@".sprintf("%d",$#children+1);
		foreach $child (@children){
#		print STDERR "^".sprintf("%d",$child->getNodeType);
			depthMap($child, $procedure);
		};
	};
#	print STDERR "*";
	&$procedure($node);
};

sub depthFilterMap {
	my ($node,$predicate,$procedure) = @_;
#	print STDERR "?";
	depthMap($node, &filterProc($predicate,$procedure));
};

sub depthOnceMap {
	my ($node, $procedure) = @_;
	if ($node->getNodeType ==  XML::DOM::ELEMENT_NODE){ 
		my @children = $node->getChildNodes;
		foreach $child (@children){
			my $result = depthOnceMap($child, $procedure);
			if ($result) {return $result};
		};
	};
	return &$procedure($node);
};

sub depthOnceFilterMap {
	my ($node,$predicate,$procedure) = @_;
#	print STDERR "?";
	depthOnceMap($node, &filterProc($predicate,$procedure));
};

sub filterProc {
	my ($predicate, $procedure) = @_;
#	print STDERR "[|";
	return sub {
		my($node)=@_;
		my $testvalue = &$predicate($node);
		if ($testvalue) {
			my $result = &$procedure($testvalue,$node);
			return $result;
		}
		else {$testvalue};
	};
};

sub checkElementTag {
	my ($tag) = @_;
#	print STDERR "~$tag";
	return sub {
		my ($node) = @_;
#		print STDERR "/$tag";
		if ($node->getNodeType == XML::DOM::ELEMENT_NODE) {
			my $tagName = $node->getTagName;
#			print STDERR ">$tagName";
			if ($tagName eq $tag) {return $tag}
			else {return 0};
		}
		else {return 0};
	};
};

sub checkNodeType {
	my ($type) = @_;
#	print STDERR "|$type";
	return sub {
		my ($node) = @_;
		my $nodeType = $node->getNodeType;
#		print STDERR "\\$type,$nodeType";
		if ($node->getNodeType == $type) {return $type}
		else {return 0};
	};
};

1;
__END__


