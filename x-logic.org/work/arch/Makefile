# $Id: Makefile.in,v 1.1.1.1 2006-04-19 20:44:51 rbj01 Exp $

BUILDFIRST=
TOPSRCDIR=../..
RELSRCDIR=/arch
RELWEBDIR=/arch
WEBROOTDIR=../
SUBDIRS=

#XML001=index.xml prosp01.xml releases.xml sources.xml workplan.xml
#HTML001=$(XML001:.xml=.html)
#HTML001i=$(XML001:.xml=-i.html)
#HTML001m=$(XML001:.xml=-m.html)

XML003= zlib-license.xml
HTML003=$(XML003:.xml=.html)

XML005=index.xml prosp01.xml releases.xml sources.xml workplan.xml

#WEBFILES=$(HTML001) $(HTML001i) $(HTML001m) $(HTML003)
WEBFILES=$(HTML005) $(HTML003)

XMLFILES=$(XML001)

ENTFILES=pp-symbol.ent

DPDIRCPY=$(ENTFILES)

include $(TOPSRCDIR)/build/rules.mk

# directories

# Paths

vpath %.in $(SRCDIR)
vpath %.xml $(SRCDIR)
vpath %.xsl $(COMDIR)

# dependencies

prosp01.xmlt: ../OpenMind/index.xmlt

index.xmlt: prosp01.xmlt releases.xmlt sources.xmlt workplan.xmlt
