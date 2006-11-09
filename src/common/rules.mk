# $Id: rules.mk,v 1.13 2006/11/09 12:05:24 rbj01 Exp $

.SUFFIXES:
.SUFFIXES: .css .doc .gif .html .img .in .sml .xml .xdoc .xsl
.PHONY: build $(SUBBUILDS) vars thisinstall $(THISINSTALL) install \
	uninstall $(UNINSTALL) $(SUBINSTALLS) isablddummy

vpath %.in $(SRCDIR)
vpath %.xsl $(COMDIR)
vpath %.sxx $(XLDPDIR)

Makefile: $(MKDEPS)
	cd $(TOPSRCDIR); ./configure --prefix=$(prefix)

# variable definitions
# the following variables should be defined in the makefile if required
# PPTHTO = (.th) names of proofpower theories for listing in TEX only
# PPTH	= (.th) names of proofpower application theories for listing in HTML
# PPPPTH	= (.th) names of proofpower built-in theories for listing in HTML
# HTML001	= (.html) HTML documents
# HTML004	= (.html) HTML documents

# The following variables are derived from the above names.

# HTML from XML

XMLT001=$(HTML001:.html=.xmlt) $(HTM001:.htm=.xmlt)
XMLT004=$(HTML004:.html=.xmlt) $(HTM004:.htm=.xmlt)

# Theory listings
# first for ProofPower built-in theories

PPPPTHD=$(PPPPTH:.th=.thd)
PPPPTHDOC=$(PPPPTH:.th=.th.doc)

# then for application theories

PPTHD=$(PPTH:.th=.thd)
PPTHDOC=$(PPTH:.th=.th.doc) $(PPPPTHDOC)
PPTHTEX=$(PPTHDOC:.doc=.tex)
HTMLTHLS=$(PPTHDOC:.th.doc=.html)
PPTHDXLD=$(PPTHDOC:.th.doc=.xml)

# Tex only theory listings

PPTHTOD=$(PPTHTO:.th=.thd)
PPTHTODOC=$(PPTHTO:.th=.th.doc)
PPTHTOTEX=$(PPTHTODOC:.doc=.tex)

# DVI, Postscript, PDF

DOCTEX=$(PPPDOC:.doc=.tex) $(PPTHTEX) $(PPTHTOTEX)
TEX=$(KLUTEX) $(DOCTEX)
KLUDVI=$(KLUTEX:.tex=.dvi)
DVI=$(TEX:.tex=.dvi)
PS=$(DVI:.dvi=.ps)
PDF=$(PS:.ps=.pdf)

# Qualified dependencies

$(KLUDVI): rbjk.bib rbjk.cls

# Qualified rules

$(XMLT001): %.xmlt: %.xml
	cp $<  $*.xmlt

$(HTML003): %.html: %.xml xslt003$(XSLTSUFF).xsl xslt002.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $< $(XLCOMDIR)/xslt003$(XSLTSUFF).xsl dir=$(BLDDIR) name=$*

$(XMLT004): %.xmlt: %.xml
	addftl <$<  >$*.xmlx
	xxml2xml <$*.xmlx >$*.xmlt

$(HTML001): %.html: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl dir=$(BLDDIR) name=$*

$(HTM001): %.htm: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl dir=$(BLDDIR) name=$*

$(HTM004): %.htm: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl pp-symbol.ent ppft.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl dir=$(BLDDIR) name=$*

$(HTML004): %.html: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl pp-symbol.ent ppft.xsl X-Logic.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl dir=$(BLDDIR) name=$*

$(HTML004i) $(HTML001i): %-i.html : %.html

$(HTML004m) $(HTML001m): %-m.html : %.html

$(HTMLTHLS): %.html: %.xml $(XLDPDIR)/xslt001s8.sxx xslt002.xsl frame01.xsl pp-symbol.ent ppft.xsl X-Logic.xsl
	xxml2xml <$*.xml >$*.xmlt
	$(JAVA) $(XSLT2PROC) -c $*.xmlt $(XLDPDIR)/xslt001s8.sxx root=$(BLDROOT) \
	dir=$(RELWEBDIR)/ name=$* imagedir=rbjgifs

$(COMDIRCPY): %: $(COMDIR)/%
	cp $(COMDIR)/$@ .

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

$(PPTHDXLD) $(PPPPTHDXLD): %.xml: %.thd
	ppthd2xml $* $(WEBROOTDIR)

$(PPDB).dbts:
	if test "$(PPDBDIR)" != ""; \
	then ln -s $(PPDBDIR)$(PPDB).$(PPDBARCH); cd ./$(PPDBDIR); $(MAKE) $(PPDB).dbts; \
	else pp_make_database -f -p $(PPBASEDB) $(PPDB); fi
	touch $(PPDB).dbts

$(PPLDS): %.lds: %.sml $(PPDB).dbts
	echo "save_and_quit();" | pp -d $(PPDB) -f $< > $*.log
	touch $@

$(PPPPTHD): %.thd: %.th
	pp_list -d $(PPBASEDB) $* > $*.thd

$(PPTHD) $(PPTHTOD): %.thd: %.th
	pp_list -d $(PPDB) $* > $*.thd

$(PPTHDOC) $(PPTHTODOC): %.th.doc: %.thd
	cp $< $*.th.doc

$(DOCTEX): %.tex: %.doc
	doctex $*
	sed -i -e "/underscoreoff/s/\([^_\]\)_/\1\\\\_/g" $*.tex

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
	texdvi -b $*
	texdvi $*
	texdvi $*

%.ps: %.dvi
	dvips $*.dvi -o $*.ps

#%.pdf: %.dvi
#	dvipdf -sPAPERSIZE=a4  $*

%.pdf: %.tex
	texpdf -b $*
	texpdf $*
	texpdf $*

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

ppthds: $(PPTHD) $(PPPPTHD)

build: $(BUILDFIRST) $(SUBBUILDS) $(BINFILES) $(DATAFILES) $(LIBFILES) $(PERLLIBFILES) \
	$(SMLLIBFILES) $(WEBFILES) $(BUILDEXTRAS)

install: build $(THISINSTALL) $(SUBINSTALLS)

# from x-logic xldoc.mk

# Variable definitions

# Qualified rules

$(XMLT005S) $(XMLT005): %.xmlt: %.xml
	addftl <$<  | xxml2xml >$*.xmlt

$(HTML005f): %.html: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl IndexFrame.xsl MainFrame.xsl pp-symbol.ent ppft.xsl X-Logic.xsl sitespecific.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl dir=$(BLDDIR) name=$*

#$(HTM005f): %.htm: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl IndexFrame.xsl MainFrame.xsl pp-symbol.ent ppft.xsl X-Logic.xsl sitespecific.xsl
#	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl dir=$(BLDDIR) name=$*

$(HTM005f): %.htm: %.xmlt $(XLDPDIR)/xslt001s8.sxx pp-symbol.ent
	$(JAVA) $(XSLT2PROC) -c $*.xmlt $(XLDPDIR)/xslt001s8.sxx root=$(BLDROOT) \
		dir=$(RELWEBDIR)/ name=$* suffix=htm imagedir=rbjgifs 

$(XFTFILES): %.xft: %.xml stripfile.xsl
	$(JAVA) $(XSLTPROC) $< $(XLCOMDIR)/stripfile.xsl dir=$(BLDDIR) name=$*
	touch $*.xft

$(HTML005i) $(HTMLTHLSi): %-i.html : %.html

$(HTML005m) $(HTMLTHLSm): %-m.html : %.html

$(HTM005i) $(HTMTHLSi): %-i.htm : %.htm

$(HTM005m) $(HTMTHLSm): %-m.htm : %.htm

$(XMLT006) $(XMLT007) $(XMLT008): %.xmlt: %.xml
	addftl <$<  | xxml2xml >$*.xmlt

$(HTML006): %.html: %.xmlt xslt001$(XSLTSUFF).xsl xslt002.xsl frame01.xsl IndexFrame.xsl MainFrame.xsl pp-symbol.ent ppft.xsl X-Logic.xsl sitespecific.xsl
	$(JAVA) $(XSLTPROC) $*.xmlt $(XLCOMDIR)/xslt001$(XSLTSUFF).xsl dir=$(BLDDIR) name=$*

$(HTML007f): %.html: %.xmlt $(XLDPDIR)/xslt001s8.sxx pp-symbol.ent
	$(JAVA) $(XSLT2PROC) -c $*.xmlt $(XLDPDIR)/xslt001s8.sxx root=$(BLDROOT) \
		dir=$(RELWEBDIR)/ name=$* imagedir=rbjgifs 

$(HTML007i) $(HTML007m): $(HTML007f)

$(HTML008): %.html: %.xmlt $(XLDPDIR)/xslt004s8.sxx pp-symbol.ent
	$(JAVA) $(XSLT2PROC) -c $*.xmlt $(XLDPDIR)/xslt004s8.sxx root=$(BLDROOT) \
		dir=$(RELWEBDIR)/ name=$* imagedir=rbjgifs 

$(ISAPDFO): %.pdf: %.ldd
	cp $*/$@ .

$(ISAPDFF): %-full.pdf: %.ldd
	cp $*/$@ .

$(ISATGZ): %.tgz: %.ldd
	cd $(TOPSRCDIR)/$(RELSRCDIR); tar cfz $(TOPSRCDIR)/build/$(RELWEBDIR)/$*.tgz $*

$(ISALDD): %.ldd : isablddummy
	cd $(TOPSRCDIR)/$(RELSRCDIR)/$*; isatool make
	touch $@

$(ISAIMG): %.img : isablddummy
	cd $(TOPSRCDIR)/$(RELSRCDIR)/$*; isatool make images
	touch $@

isablddummy:
