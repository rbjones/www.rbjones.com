# $Id: smlcm.mk,v 1.1.1.1 2006-04-19 20:44:51 rbj01 Exp $

.SUFFIXES: .cm .cmlog .log .siglog .smllog .smlcmdbts .xml

# variable definitions

CMLOGFILES=$(CMFILES:.cm=.cmlog)
SMLLOGFILES=$(SMLFILES:.sml=.smllog)
SIGLOGFILES=$(SIGFILES:.sig=.siglog)
LOGFILES=$(CMLOGFILES) $(SMLLOGFILES) $(SIGLOGFILES)

# Qualified rules

$(SCDB).smlcmdbts:
	if test "$(SCDBDIR)" != ""; then ln -s $(SCDBDIR)$(SCDB).smlcmdbts; fi
	cd ./$(SCDBDIR); if test ! -f $(SCDB).smlcmdbts; \
	then echo "SMLofNJ.exportML \"$(SCDB)\";" \
	     | $(SML-CM); touch $(SCDB).smlcmdbts; \
	fi

$(CMLOGFILES): %.cmlog: %.cm $(SCDB).smlcmdbts
	echo "CM.make' \"$<\"; SMLofNJ.exportML \"$(SCDBDIR)$(SCDB)\";" \
        | $(SML-CM) @SMLload=$(SCDBDIR)$(SCDB) >$@

$(SIGLOGFILES): %.siglog: %.sig $(SCDB).smlcmdbts
	echo "use \"$<\"; SMLofNJ.exportML \"$(SCDBDIR)$(SCDB)\";" \
	| $(SML-CM) @SMLload=$(SCDBDIR)$(SCDB) >$@

$(SMLLOGFILES): %.smllog: %.sml $(SCDB).smlcmdbts
	echo "use \"$<\"; SMLofNJ.exportML \"$(SCDBDIR)$(SCDB)\";" \
	| $(SML-CM) @SMLload=$(SCDBDIR)$(SCDB) >$@

$(XFTCMFILES): %.cm: %.xft

$(XFTSMLFILES): %.sml: %.xft

smlcm:
	@echo "sml-cm @SMLload=$(SCDBDIR)$(SCDB)"
