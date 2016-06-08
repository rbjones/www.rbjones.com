# $Id: Makefile.in,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $

TOPSRCDIR=../../../..
RELSRCDIR=/pp/gst/tok
RELWEBDIR=/pp/gst/tok
WEBROOTDIR=../../../
SUBDIRS=

PPDB=xlpp
PPDBDIR=../../
PPXML=dichotomies.xml tractatus.xml xl-metamod1.xml
PPDOC=$(PPXML:.xml=.doc)
PPLDS=$(PPXML:.xml=.lds)
PPTH=dichot.th tract.th xl-mm1.th
PPTHD=$(PPTH:.th=.thd)

XML005=$(PPXML) index.xml
#HTML004=$(XML004:.xml=.html)
#HTML004i=$(XML004:.xml=-i.html)
#HTML004m=$(XML004:.xml=-m.html)

HTMLTHLSi=$(HTMLTHLS:.html=-i.html)
HTMLTHLSm=$(HTMLTHLS:.html=-m.html)

SRCDIRCPY=$(XML005)

ENTFILES=pp-symbol.ent

DPDIRCPY=$(ENTFILES)

WEBFILES=$(HTML005) $(HTMLTHLS) $(HTMLTHLSi) $(HTMLTHLSm)

include $(TOPSRCDIR)/build/rules.mk

# directories

# Paths

vpath %.in $(SRCDIR)
vpath %.xsl $(COMDIR)

# Rules

index.html: dichotomies.xmlt tractatus.xmlt xl-metamod1.xmlt

dichotomies.lds: ../gst-final.lds

dichot.th: dichotomies.lds
	touch dichot.th

tractatus.lds: ../gst-final.lds

tract.th: tractatus.lds
	touch tract.th

xl-mm1.lds: ../gst-final.lds

xl-mm1.th: xl-metamod1.lds
	touch xl-mm1.th
