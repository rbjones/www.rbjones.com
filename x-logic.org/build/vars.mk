# $Id: vars.mk.in,v 1.3 2010-04-14 21:54:11 rbj Exp $
# build/vars.mk.  Generated from vars.mk.in by configure.


prefix=/usr/local/rbj
exec_prefix=${prefix}

displayvars:
	@echo "prefix = /usr/local/rbj"
	@echo "exec_prefix = ${prefix}"
	@echo "bindir = ${exec_prefix}/bin"
	@echo "datadir = ${prefix}/share"
	@echo "libdir = ${exec_prefix}/lib"
	@echo "includedir = ${prefix}/include"
	@echo "infodir = ${prefix}/share/info"
	@echo "libexecdir = ${exec_prefix}/libexec"
	@echo "localstatedir = ${prefix}/var"
	@echo "mandir = ${prefix}/share/man"
	@echo "oldincludedir = /usr/include"	
	@echo "sbindir = ${exec_prefix}/sbin"
	@echo "sharedstatedir = ${prefix}/com"
	@echo "srcdir = ."
	@echo "sysconfdir = ${prefix}/etc"
	@echo "top_srcdir = .."

	@echo	"x-logic makefile help text"
	@echo   "SML = $(SML)"
	@echo   "SML-CM = $(SML-CM)"
	@echo 	"bin:	$(BINFILES)"
	@echo 	"data:	$(DATAFILES)"
	@echo 	"lib:	$(LIBFILES)"
	@echo 	"perllib:	$(PERLLIBFILES)"
	@echo 	"web:	$(WEBFILES)"
#	@echo	"build:	bin data lib web"
#	@echo	"export"
	@echo 	"BINDIR=		$(BINDIR)"
	@echo 	"BUILDDIR=		$(BUILDDIR)"
	@echo 	"DATADIR=	$(DATADIR)"
	@echo 	"RDATADIR=	$(RDATADIR)"
	@echo 	"LIBDIR=		$(LIBDIR)"
	@echo 	"PERLLIBDIR=	$(PERLLIBDIR)"
	@echo 	"WEBDIR=	$(WEBDIR)"
	@echo 	"RWEBDIR=	$(RWEBDIR)"
	@echo	"SUBDIRS:	$(SUBDIRS)"
	@echo	"COMDIR:	$(COMDIR)"
	@echo	"THISINSTALL:	$(THISINSTALL)"

SHELL = /bin/sh

INSTALL=/usr/bin/install
JAVA=/usr/bin/java
MAKE=/usr/bin/make
PERL=/usr/bin/perl
SML=:
SML-CM=$(SML)-cm
# You may need to change these hard coded values
# if you have installed fxp somewhere else
FXPLIB=/usr/local/fxp/lib
FXPAPPS=/usr/local/fxp/fxp-1.4.1/src/Apps

MKFILES=build/isabelle.mk build/project.mk build/rules.mk build/xldoc.mk 
MKDEPS=$(TOPSRCDIR)/config.status \
	$(TOPSRCDIR)/Makefile.in \
	$(TOPSRCDIR)/arch/Makefile.in \
	$(TOPSRCDIR)/root/Makefile.in \
	$(TOPSRCDIR)/arch/Makefile.in \
	$(TOPSRCDIR)/build/Makefile.in \
	$(TOPSRCDIR)/build/vars.mk.in \
	$(TOPSRCDIR)/build/project.mk \
	$(TOPSRCDIR)/build/docprep/Makefile.in \
	$(TOPSRCDIR)/isabelle/Makefile.in \
	$(TOPSRCDIR)/isabelle/tok/Makefile.in \
	$(TOPSRCDIR)/isabelle/xml/Makefile.in \
	$(TOPSRCDIR)/OpenMind/Makefile.in \
	$(TOPSRCDIR)/sml/Makefile.in \
	$(TOPSRCDIR)/root/Makefile.in \
	$(TOPSRCDIR)/pp/Makefile.in \
	$(TOPSRCDIR)/pp/holzfc/Makefile.in \
	$(TOPSRCDIR)/pp/gst/Makefile.in \
	$(TOPSRCDIR)/pp/gst/tok/Makefile.in \
	$(TOPSRCDIR)/pp/gst/xml/Makefile.in

# Change this if you are using a different java XSLT processor.
# You may also have to change rules.mk.in which thinks it knows how to run it.
#XSLTPROC=com.jclark.xsl.sax.Driver
#XSLTPROC=com.icl.saxon.StyleSheet
XSLTPROC=net.sf.saxon.Transform
XSLTCOMP=net.sf.saxon.Compile
#This is a stylesheet name suffix to permit selection of then top level stylesheet appropriate
#for a particular XSLT processor.
#No suffix for James Clark's XT.
#XSLTSUFF=s8
#Suffix "s" for Mike Kay/ICL's saxon version 6 (XSLT 1.0), s8 for saxonb8 (XSLT 2.0).
XSLTSUFF=s

BUILDDIR=$(TOPSRCDIR)/build
include $(BUILDDIR)/project.mk

DATADIR=${prefix}/share/$(THISPROJ)
WEBDIR=$(DATADIR)/$(THISPROJ)
BINDIR=${exec_prefix}/bin/$(THISPROJ)
LIBDIR=${exec_prefix}/lib/$(THISPROJ)
PERLLIBDIR=$(LIBDIR)/$(PERLLIBNAME)
SMLLIBDIR=$(LIBDIR)/$(SMLLIBNAME)

DPDIR=$(BUILDDIR)/docprep
DOCPREPDATA=$(DATADIR)/docprep
PPDOCSML=$(PPDOC:.doc=.sml)
PPDOCXDOC=$(PPDOC:.doc=.xdoc)
PPDOCSMLO=$(PPDOC:.doc=.smlo)
RDATADIR=$(DATADIR)$(RELDATADIR)
RWEBDIR=$(WEBDIR)$(RELWEBDIR)
ROOTDIR=$(TOPSRCDIR)/root
SRCDIR=$(TOPSRCDIR)$(RELSRCDIR)
SUBBUILDS=$(SUBDIRS:=.build)
SUBINSTALLS=$(SUBDIRS:=.install)

#PPDBARCH=x86-linux
PPDBARCH=polydb
PPHOLDB=$(PPDB).$(PPDBARCH)
