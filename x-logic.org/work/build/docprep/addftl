#!/usr/bin/perl -w
# ($Id)
# For preprocessing an XML file containing xld:ft sections before
# transforming into XHTML using XT.
# Encloses each line in formal text sections with <xld:ftl></xld:ftl> markers.

use XML::DOM;
use XLogic::DomXtras;

XML::DOM::setTagCompression (\&tag_compression);

my $parser = new XML::DOM::Parser;
my $doc = $parser->parse (*STDIN);

&XLogic::DomXtras::depthFilterMap
	($doc->getDocumentElement,
	 XLogic::DomXtras::checkElementTag("ft"),
	 \&procFtElement);

&XLogic::DomXtras::depthFilterMap
	($doc->getDocumentElement,
	 XLogic::DomXtras::checkElementTag("holsig"),
	 \&procHolconstElement);

&XLogic::DomXtras::depthFilterMap
	($doc->getDocumentElement,
	 XLogic::DomXtras::checkElementTag("holpred"),
	 \&procHolconstElement);

print $doc->toString;

# this procedure removes a leading newline in an <ft> node.
sub ftFirstTextNodeConv {
	my ($nodetype, $node) = @_;
	my $text = $node->getNodeValue;
	if ($text =~ s/^\s*\n//){$node->setNodeValue($text)};
	return 1;
};

# this procedure adds markup for linebreaks in the TEXT nodes of <ft> sections.
sub ftTextNodeConv {
	my ($nodetype, $node) = @_;
	my $parent = $node->getParentNode;
	my $text = $node->getNodeValue;
	my $oldDelimiter="";
#	print STDERR "!{$nodetype,$text}\n";
	while ($text =~ s/^([^\n\t]*)(\n *|\t)//){
#		print STDERR "<";
		$firsttext=$1; $delimiter=$2;
#			print STDERR "*{$firsttext$delimiter}\n";
		if ($firsttext) {
			my $newTextNode =  $doc->createTextNode ($oldDelimiter.$firsttext);
			$parent->insertBefore($newTextNode, $node)
			};
		my $newElement;
		if ($delimiter ne "\t"){
			$indent=length($delimiter)-1;
			$newElement=$doc->createElement("ftbr");
			if ($indent) {$newElement->setAttribute("indent",$indent)};
			$oldDelimiter=$delimiter}
		else {
			$newElement=$doc->createElement("fttab");
			$oldDelimiter=""};
		$parent->insertBefore($newElement, $node);
	};					
#		print STDERR "*{$oldDelimiter$text}\n";
	$node->setNodeValue($oldDelimiter.$text);
};

sub procFtElement {
	my($testresult, $node)=@_;
#	print STDERR "[&{$testresult}\n";
	&XLogic::DomXtras::depthOnceFilterMap
		($node,
		 XLogic::DomXtras::checkNodeType(XML::DOM::TEXT_NODE),
		 \&ftFirstTextNodeConv);
	&XLogic::DomXtras::depthFilterMap
		($node,
		 XLogic::DomXtras::checkNodeType(XML::DOM::TEXT_NODE),
		 \&ftTextNodeConv);
#	print STDERR "]";
};

sub procHolconstElement {
	my($testresult, $node)=@_;
	&XLogic::DomXtras::depthOnceFilterMap
		($node,
		 XLogic::DomXtras::checkNodeType(XML::DOM::TEXT_NODE),
		 \&ftFirstTextNodeConv);
	&XLogic::DomXtras::depthFilterMap
		($node,
		 XLogic::DomXtras::checkNodeType(XML::DOM::TEXT_NODE),
		 \&ftTextNodeConv);
#	print STDERR "]";
};

sub tag_compression{
	my ($tag, $elem) = @_;
# Print empty br, hr and img tags like this: <br />
#	return 2 if $tag =~ /^(br|hr|img)$/;
# Print other empty tags like this: <empty></empty>
#	return 1;
	return 2
};
