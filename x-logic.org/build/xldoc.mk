# $Id: xldoc.mk,v 1.1.1.1 2006-04-19 20:44:51 rbj01 Exp $

.SUFFIXES: .html .xml .xsl .xmlt

# Variable definitions

XMLT005=$(XML005:.xml=.xmlt)
HTML005f=$(XML005:.xml=.html)
HTML005i=$(XML005:.xml=-i.html)
HTML005p=$(XML005:.xml=-i.php)
HTML005m=$(XML005:.xml=-m.html)
HTML005=$(HTML005f) $(HTML005i) $(HTML005m) $(HTML005p)

# Qualified rules

$(XMLT005): %.xmlt: %.xml
	addftl <$<  | xxml2xml >$*.xmlt

$(HTML005f): %.html: %.xmlt xslt001p$(XSLTSUFF).xsl xslt002.xsl frame01p.xsl IndexFramep.xsl MainFrame.xsl pp-symbol.ent ppft.xsl X-Logic.xsl sitespecific.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(COMDIR)/xslt001p$(XSLTSUFF).xsl

$(XFTFILES): %.xft: %.xml stripfile.xsl
	$(JAVA) com.jclark.xsl.sax.Driver $< $(COMDIR)/stripfile.xsl
	touch $*.xft

$(HTML005i): %-i.html : %.html

$(HTML005p): %-i.php : %.html

# Unqualified rules


# specific rules

