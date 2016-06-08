# $Id: Makefile.in,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $

TOPSRCDIR=../..
RELSRCDIR=/OpenMind
RELWEBDIR=/OpenMind

XML005=index.xml foundAnaly.xml TheoryOfKnowledge.xml host.xml
#HTML001=$(XML001:.xml=.html)
#HTML001i=$(XML001:.xml=-i.html)
#HTML001m=$(XML001:.xml=-m.html)
XML003=
HTML003=$(XML003:.xml=.html)
#WEBFILES=$(HTML001) $(HTML001i) $(HTML001m) $(HTML003)
WEBFILES=$(HTML005) $(HTML003)

ENTFILES=pp-symbol.ent

DPDIRCPY=$(ENTFILES)

include $(TOPSRCDIR)/build/rules.mk

# directories

# Paths

vpath %.in $(SRCDIR)
vpath %.xml $(SRCDIR)
vpath %.xsl $(COMDIR)

#dependencies

index.xmlt: foundAnaly.xmlt TheoryOfKnowledge.xmlt

foundAnaly.xmlt: host.xmlt

host.xmlt: ../pp/holzfc/holzfc1.xmlt ../pp/gst/index.xmlt




