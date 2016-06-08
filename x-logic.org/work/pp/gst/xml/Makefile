# $Id: Makefile.in,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $

TOPSRCDIR=../../../..
RELSRCDIR=/pp/gst/xml
RELWEBDIR=/pp/gst/xml
WEBROOTDIR=../../../
SUBDIRS=

PPDB=xlpp
PPDBDIR=../../
PPXML=infoset.xml xmlparse.xml
PPDOC=$(PPXML:.xml=.doc)
PPLDS=$(PPXML:.xml=.lds)
PPTH=
PPTHD=$(PPTH:.th=.thd)

XML005=$(PPXML)
#HTML004=$(XML004:.xml=.html)
#HTML004i=$(XML004:.xml=-i.html)
#HTML004m=$(XML004:.xml=-m.html)

HTMLTHLSi=$(HTMLTHLS:.html=-i.html)
HTMLTHLSm=$(HTMLTHLS:.html=-m.html)

SRCDIRCPY=$(XML005)

ENTFILES=pp-symbol.ent

DPDIRCPY=$(ENTFILES)

XFTFILES=xmlparse.xft

WEBFILES=$(HTML005) $(HTMLTHLS) $(HTMLTHLSi) $(HTMLTHLSm)

include $(TOPSRCDIR)/build/rules.mk

# directories

# Paths

vpath %.in $(SRCDIR)
vpath %.xsl $(COMDIR)

# Rules

fxlib.cm:
	echo "Alias $(FXPLIB)/fxlib.cm" >> fxlib.cm

xmlparse.cm: xmlparse.xft

xmlparse.log: xmlparse.cm xmlparse.sml

