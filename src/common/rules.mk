# $Id: rules.mk,v 1.3 2004/03/11 10:44:05 rbj Exp $

.SUFFIXES:
.SUFFIXES: .css .doc .gif .html .in .sml .xml .xdoc .xsl
.PHONY: build $(SUBBUILDS) vars thisinstall $(THISINSTALL) install \
	uninstall $(UNINSTALL) $(SUBINSTALLS)

vpath *.in $(SRCDIR)
vpath *.xsl $(COMDIR)

Makefile: $(MKDEPS)
	cd $(TOPSRCDIR); ./configure --prefix=$(prefix)

# variable definitions
# the following variables should be defined in the makefile if required
# PPTH	= (.th) names of proofpower theories for listing 
# HTML001	= (.html) HTML documents
# HTML004	= (.html) HTML documents

# The following variables are derived from the above names.

# HTML from XML

XMLT001=$(HTML001:.html=.xmlt)
XMLT004=$(HTML004:.html=.xmlt)

# Theory listings

PPTHD=$(PPTH:.th=.thd)
PPTHDOC=$(PPTH:.th=.th.doc)
PPTHTEX=$(PPTHDOC:.doc=.tex)
HTMLTHLS=$(PPTHDOC:.th.doc=.html)
PPTHDXLD=$(PPTHDOC:.th.doc=.xml)

# DVI, Postscript, PDF

TEX=$(PPPDOC:.doc=.tex)
DVI=$(TEX:.tex=.dvi)
PS=$(DVI:.dvi=.ps)
PDF=$(PS:.ps=.pdf)

# Qualified rules

$(XMLT001): %.xmlt: %.xml
	cp $<  $*.xmlt

$(HTML003): %.html: %.xml xslt003$(XSLTSUFF).xsl xslt002.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $< $(XLCOMDIR)/xslt003$(XSLTSUFF).xsl

$(XMLT004): %.xmlt: %.xml
	addftl <$<  >$*.xmlx
	xxml2xml <$*.xmlx >$*.xmlt

$(HTML001): %.html: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl

$(HTML004): %.html: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl pp-symbol.ent ppft.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl

$(HTML004i) $(HTML001i): %-i.html : %.html

$(HTML004m) $(HTML001m): %-m.html : %.html

$(HTMLTHLS): %.html: %.xml xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl pp-symbol.ent ppft.xsl X-Logic.xsl
	xxml2xml <$*.xml >$*.xmlt
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl

$(DPDIRCPY): %: $(DPDIR)/%
	cp $(DPDIR)/$@ .

$(SRCDIRCPY): %: $(SRCDIR)/%
	cp $(SRCDIR)/$@ .

$(XLCDIRCPY): %: $(XLCOMDIR)/%
	cp $(XLCOMDIR)/$@ .

$(XLDPDIRCPY): %: $(XLDPDIR)/%
	cp $(XLDPDIR)/$@ .

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

$(PPTHDOC): %.th.doc: %.thd
	cp $< $*.th.doc

$(PPTHTEX): %.tex: %.doc
	doctex $*

$(BASHBIN): % : %.sh
	cp $< $*
	chmod +x $*

$(PERLBIN): % : %.pl
	cp $< $*
	chmod +x $*

# Unqualified rules

%.tex: %.doc
	doctex $*

%.dvi: %.tex
	latex $*.tex
	latex $*.tex
	latex $*.tex

%.ps: %.dvi
	dvips $*.dvi -o $*.ps

%.pdf: %.ps
	ps2pdf $<

%.gz: %
	gzip --best --stdout $< > $<.gz

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

installweb: $(WEBFILES)
	@if ! test -d $(RWEBDIR) &&  test "" != "$(WEBFILES)"; then $(INSTALL) -d -m 755 $(RWEBDIR); fi
	if test "" != "$(WEBFILES)"; then $(INSTALL) -m 644 $(WEBFILES) $(RWEBDIR); fi

THISINSTALL=installweb installdata installbins installlibs installperllibs installsmllibs

ppthds: $(PPTHD)

build: $(BUILDFIRST) $(SUBBUILDS) $(BINFILES) $(DATAFILES) $(LIBFILES) $(PERLLIBFILES) \
	$(SMLLIBFILES) $(WEBFILES) $(BUILDEXTRAS)

install: build $(THISINSTALL) $(SUBINSTALLS)

# from x-logic xldoc.mk

# Variable definitions


# Qualified rules

$(XMLT005): %.xmlt: %.xml
	addftl <$<  | xxml2xml >$*.xmlt

$(HTML005f): %.html: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl IndexFrame.xsl MainFrame.xsl pp-symbol.ent ppft.xsl X-Logic.xsl sitespecific.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl

$(XFTFILES): %.xft: %.xml stripfile.xsl
	$(JAVA) com.jclark.xsl.sax.Driver $< $(XLCOMDIR)/stripfile.xsl
	touch $*.xft

$(HTML005i): %-i.html : %.html

$(HTML005m): %-m.html : %.html

$(XMLT006): %.xmlt: %.xml
	addftl <$<  | xxml2xml >$*.xmlt

$(HTML006): %.html: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl IndexFrame.xsl MainFrame.xsl pp-symbol.ent ppft.xsl X-Logic.xsl sitespecific.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl

