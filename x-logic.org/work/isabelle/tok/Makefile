# $Id: Makefile.in,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $

TOPSRCDIR=../../..
RELSRCDIR=/isabelle/tok
RELWEBDIR=/isabelle/tok
WEBROOTDIR=../../
SUBDIRS=

ISAXML=xl-metamod2.xml
ISATH=XLMM2.th
ISADB=xl
ISADBINIT=HOL
ISADBDIR=../

XML005=$(ISAXML) index.xml
#XML004=$(ISAXML) index.xml
#HTML004=$(XML004:.xml=.html)
#HTML004i=$(XML004:.xml=-i.html)
#HTML004m=$(XML004:.xml=-m.html)

ISATHTMLi=$(ISATHTML:.html=-i.html)
ISATHTMLm=$(ISATHTML:.html=-m.html)
ISATHTMLS=$(ISATHTML) $(ISATHTMLi) $(ISATHTMLm)

SRCDIRCPY=$(XML005)

ENTFILES=pp-symbol.ent

DPDIRCPY=$(ENTFILES)

WEBFILES=$(HTML005)

include $(TOPSRCDIR)/build/rules.mk
include $(TOPSRCDIR)/build/isabelle.mk

# directories

# Paths

vpath %.in $(SRCDIR)
vpath %.xsl $(COMDIR)

# Rules

index.html: xl-metamod2.xmlt

makefile: $(TOPSRCDIR)/build/isabelle.mk

XLMM2.thy: xl-metamod2.xft



