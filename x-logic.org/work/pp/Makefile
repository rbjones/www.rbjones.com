# $Id: Makefile.in,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $

BUILDFIRST=pp-smlxtras.lds
TOPSRCDIR=../..
RELSRCDIR=/pp
RELWEBDIR=/pp
WEBROOTDIR=../
SUBDIRS=holzfc gst

PPDB=xlpp
PPDBDIR=
PPXML=pp-smlxtras.xml
PPDOC=$(PPXML:.xml=.doc)
PPLDS=$(PPXML:.xml=.lds)
PPTH= min.th log.th init.th misc.th pair.th list.th char.th
PPTHD=$(PPTH:.th=.thd)

XML005=$(PPXML) index.xml pptheories.xml
#HTML004=$(XML004:.xml=.html)
#HTML004i=$(XML004:.xml=-i.html)
#HTML004m=$(XML004:.xml=-m.html)

XMLFILES=$(XML005)

HTMLTHLSi=$(HTMLTHLS:.html=-i.html)
HTMLTHLSm=$(HTMLTHLS:.html=-m.html)

ENTFILES=pp-symbol.ent

DPDIRCPY=$(ENTFILES)
SRCDIRCPY=

WEBFILES=$(HTML005) $(HTMLTHLS) $(HTMLTHLSi) $(HTMLTHLSm)

include $(TOPSRCDIR)/build/rules.mk

# directories

# Paths

vpath %.in $(SRCDIR)
vpath %.xml $(SRCDIR)
vpath %.xsl $(COMDIR)

# Rules

$(PPTH): $(PPDB).dbts 
	touch $@

index.html: pp-smlxtras.xmlt pptheories.xmlt holzfc/index.xmlt gst/index.xmlt

