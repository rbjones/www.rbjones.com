# $Id: isabelle.mk,v 1.1.1.1 2006-04-19 20:44:51 rbj01 Exp $

.SUFFIXES: .html .lml .ML .MLlog .syd .thd .thy .thylog .xml

# variable definitions

ISAXFT=$(ISAXML:.xml=.xft)
ISATHY=$(ISATH:.th=.thy)
ISAML=$(ISATH:.th=.ML)
ISALML=$(ISATH:.th=.lml)
ISASYD=$(ISATH:.th=.syd)
ISATHD=$(ISATH:.th=.thd)
ISATXML=$(ISATH:.th=.xml)
ISATHTML=$(ISATH:.th=.html)

# Qualified rules

$(ISAML): %.ML : %.thy

$(ISAXFT): %.xft: %.xml stripfile.xsl
	$(JAVA) com.jclark.xsl.sax.Driver $*.xml $(COMDIR)/stripfile.xsl

$(ISATXML): %.xml: %.syd %.thd
	touch $@

$(ISATHTML): %.html: %.xml xslt001.xsl xslt002.xsl frame01.xsl pp-symbol.ent ppft.xsl
#	xxml2xml <$*.xml >$*.xmlt
	$(JAVA) com.jclark.xsl.sax.Driver $*.xml $(COMDIR)/isabelle-thl.xsl

ISATHDXLD=$(ISATHD:.thd=.xml)

$(ISATHDXLD): %.xml: %.thd
#	ppthd2xml $* $(WEBROOTDIR)

$(ISADB).dbts:
	if test "$(ISADBDIR)" != ""; then ln -s $(ISADBDIR)$(ISADB).dbts; fi
	cd ./$(ISADBDIR); if test ! -f $(ISADB).dbts; \
	then isabelle -q $(ISADBINIT) $(ISADB); touch $(ISADB).dbts; fi

$(ISALML): %.lml: %.thy %.ML $(ISADB).dbts
	isabelle -e 'use_thy "$*";' -q $(ISADB) > $*.thylog
	touch $@

$(ISATHD): %.thd: %.lml
	isabelle -e "print_theory $*.thy;" -q $(ISADB) > $*.thd

$(ISASYD): %.syd: %.lml
	echo "print_syntax $*.thy;" | isabelle $(ISADB) > $*.syd

isathds: $(ISATHD) $(ISASYD)










