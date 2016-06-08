# $Id: rules.mk,v 1.1.1.1 2006-04-19 20:44:51 rbj01 Exp $

.SUFFIXES:
.SUFFIXES: .css .doc .gif .html .in .sml .xml .xdoc .xsl
.PHONY: build $(SUBBUILDS) vars thisinstall $(THISINSTALL) install \
	uninstall $(UNINSTALL) $(SUBINSTALLS)

BUILDDIR=$(TOPSRCDIR)/build
include $(BUILDDIR)/project.mk
include $(BUILDDIR)/vars.mk
include $(BUILDDIR)/xldoc.mk
include $(BUILDDIR)/smlcm.mk

vpath *.in $(SRCDIR)
vpath *.xsl $(COMDIR)

Makefile: $(MKDEPS)
	cd $(TOPSRCDIR); ./configure

# Qualified rules

XMLT001=$(HTML001:.html=.xmlt)

$(XMLT001): %.xmlt: %.xml
	cp $<  $*.xmlt

$(HTML003): %.html: %.xml xslt003$(XSLTSUFF).xsl xslt002.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $< $(COMDIR)/xslt003$(XSLTSUFF).xsl path=$*

XMLT004=$(HTML004:.html=.xmlt)

$(XMLT004): %.xmlt: %.xml
	addftl <$<  >$*.xmlx
	xxml2xml <$*.xmlx >$*.xmlt

$(HTML001): %.html: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(COMDIR)/xslt001$(XSLTSUFF).xsl path=$*

$(HTML004): %.html: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl pp-symbol.ent ppft.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(COMDIR)/xslt001$(XSLTSUFF).xsl path=$*

$(HTML004i) $(HTML001i): %-i.html : %.html

$(HTML004m) $(HTML001m): %-m.html : %.html

HTMLTHLS=$(PPTHD:.thd=.html)

$(HTMLTHLS): %.html: %.xml xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl pp-symbol.ent ppft.xsl X-Logic.xsl
	xxml2xml <$*.xml >$*.xmlt
	$(JAVA) $(XSLTPROC) $*.xmlt $(COMDIR)/xslt001$(XSLTSUFF).xsl path=$*

$(DPDIRCPY): %: $(DPDIR)/%
	cp $(DPDIR)/$@ .

$(SRCDIRCPY): %: $(SRCDIR)/%
	cp $(SRCDIR)/$@ .

$(SUBINSTALLS): %.install: 
	cd $* && $(MAKE) install

$(SUBBUILDS): %.build: 
	cd $* && $(MAKE) build

$(PPDOC): %.doc : %.xml
	xml2ppdoc <$^ >$*.doc

$(PPDOCSML): %.sml: %.doc
	docsml -f $(DOCPREPDATA)/sieveview $*

$(PPDOCXDOC): %.xdoc:
	ppdoc2xml <$*.doc >$(SRCDIR)/$*.xml

%.xmldoc: %.doc
	sieve -f $(DOCPREPDATA)/sieveview xmldoc <$*.doc >$*.xmldoc

PPTHDXLD=$(PPTHD:.thd=.xml)

$(PPTHDXLD): %.xml: %.thd
	ppthd2xml $* $(WEBROOTDIR)

$(PPDB).dbts:
	if test "$(PPDBDIR)" != ""; then ln -s $(PPDBDIR)$(PPDB).$(PPDBARCH); fi
	cd ./$(PPDBDIR); if test ! -f $(PPDB).$(PPDBARCH); then pp_make_database -p hol $(PPDB); fi
	touch $(PPDB).dbts

$(PPLDS): %.lds: %.sml $(PPDB).dbts
	echo "save_and_quit();" | pp -d $(PPDB) -f $< > $*.log
	touch $@

$(PPTHD): %.thd: %.th
	pp_list -d $(PPDB) $* > $*.thd

$(BASHBIN): % : %.sh
	cp $< $*
	chmod +x $*

$(PERLBIN): % : %.pl
	cp $< $*
	chmod +x $*

$(XSLBIN): %.sxx: %.xsl
	$(JAVA) $(XSLTCOMP) $< $*.sxx

# Unqualified rules


# specific rules

installbins:
	@if ! test -d $(BINDIR) &&  test "" != "$(BINFILES)"; then $(INSTALL) -d -m 755 $(BINDIR); fi
	if test "" != "$(BINFILES)"; then $(INSTALL) -m 755 $(BINFILES) $(BINDIR); fi

installdata:
	@if ! test -d $(RDATADIR) && test "" != "$(DATAFILES)"; then $(INSTALL) -d -m 755 $(RDATADIR); fi
	if test "" != "$(DATAFILES)"; then $(INSTALL) -m 644 $(DATAFILES) $(RDATADIR); fi

installlibs:
	@if ! test -d $(LIBDIR) &&  test "" != "$(LIBFILES)"; then $(INSTALL) -d -m 755 $(LIBDIR); fi
	if test "" != "$(LIBFILES)"; then $(INSTALL) -m 644 $(LIBFILES) $(LIBDIR); fi	

installperllibs:
	@if ! test -d $(PERLLIBDIR) &&  test "" != "$(PERLLIBFILES)"; then $(INSTALL) -d -m 755 $(PERLLIBDIR); fi
	if test "" != "$(PERLLIBFILES)"; then $(INSTALL) -m 644 $(PERLLIBFILES) $(PERLLIBDIR); fi	

installsmllibs:
	@if ! test -d $(SMLLIBDIR) &&  test "" != "$(SMLLIBFILES)"; \
	then $(INSTALL) -d -m 755 $(SMLLIBDIR); fi
	if test "" != "$(SMLLIBFILES)"; \
	then $(INSTALL) -m 644 $(SMLLIBFILES) $(SMLLIBDIR); cp -r CM $(SMLLIBDIR); fi

installweb:
	@if ! test -d $(RWEBDIR) &&  test "" != "$(WEBFILES)"; then $(INSTALL) -d -m 755 $(RWEBDIR); fi
	if test "" != "$(WEBFILES)"; then $(INSTALL) -m 644 $(WEBFILES) $(RWEBDIR); fi

THISINSTALL=installweb installdata installbins installlibs installperllibs installsmllibs

ppthds: $(PPTHD)

build: $(BUILDFIRST) $(SUBBUILDS) $(BINFILES) $(DATAFILES) $(LIBFILES) $(PERLLIBFILES) \
	$(SMLLIBFILES) $(WEBFILES)

install: build $(THISINSTALL) $(SUBINSTALLS)

