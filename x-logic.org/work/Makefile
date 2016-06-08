# $Id: Makefile.in,v 1.4 2010-04-14 21:54:11 rbj Exp $

TOPSRCDIR=..
RELSRCDIR=/root
RELWEBDIR=/.

ENTFILES=pp-symbol.ent
DPDIRCPY=$(ENTFILES)
SRCDIRCPY=copyright.txt robots.txt 
SUBDIRS= build #OpenMind arch pp
#SUBDIRS= build isabelle pp OpenMind arch

XML003=index.xml
HTML003=$(XML003:.xml=.html)

XML005=directories.xml
#HTML004=$(XML004:.xml=.html)
#HTML004i=$(XML004:.xml=-i.html)
#HTML004m=$(XML004:.xml=-m.html)

#WEBFILES=$(HTML003) $(SRCDIRCPY) $(HTML005)

include $(TOPSRCDIR)/build/rules.mk

# directories

# Paths

vpath %.in $(SRCDIR)
vpath %.xml $(SRCDIR)
vpath %.xsl $(COMDIR)

#dependencies

directories.html: sml/index.xmlt












