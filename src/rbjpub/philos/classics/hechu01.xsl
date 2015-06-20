<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
		version="1.0"
                xmlns:xt="http://www.jclark.com/xt"
                xmlns:ns1="http://www.rbjones.com/xmlns/ns1"
                extension-element-prefixes="xt">

<xsl:output name="main" method="html" version="4.0" encoding="ASCII" indent="yes"/>

<xsl:template match="ns1:part">

 <xsl:result-document href="{@file}" format="main">
<xsl:text disable-output-escaping="yes">&lt;!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.0 Transitional//EN"&gt;</xsl:text>
  <xsl:text>&#xA;</xsl:text>
<HTML>
<HEAD>
<LINK REL="STYLESHEET" TYPE="text/css" HREF="{@rbjpub}prof/p1sty.txt" TITLE="Factasia"/>
<TITLE>MainFrame:<xsl:value-of select="@title"/></TITLE>
</HEAD>
<BODY CLASS="{@class}">
<CENTER>
<H3><xsl:value-of select="@section"/></H3>
<H2><xsl:value-of select="@heading"/></H2>
<H3><xsl:value-of select="@part"/></H3>
</CENTER>
    <xsl:apply-templates/>
<CENTER>
<A TARGET="MainFrame" HREF="index.htm"><IMG SRC="{@rbjpub}../rbjgifs/up.gif" ALT="up" BORDER="0" ALIGN="BOTTOM"/></A>
  <xsl:text>&#xA;</xsl:text>
<A TARGET="_top" HREF="{@rbjpub}index.htm"><IMG SRC="{@rbjpub}../rbjgifs/home.gif" ALT="quick index" BORDER="0" ALIGN="BOTTOM"/></A>
  <xsl:text>&#xA;</xsl:text>
<A TARGET="_top" HREF="{@rbjpub}rbj.htm"><IMG SRC="{@rbjpub}../rbjgifs/rbjin1.gif" ALT="RBJ" BORDER="0" ALIGN="TOP"/></A>
created <xsl:value-of select="@created"/> modified <xsl:value-of select="@modified"/>
  <xsl:text>&#xA;</xsl:text>
</CENTER>
</BODY>
</HTML>
  </xsl:result-document>

  <xsl:text>Created : </xsl:text>
  <xsl:value-of select="@file"/>
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template match="p">
	<xsl:copy>
    	<xsl:apply-templates/>
	</xsl:copy>
</xsl:template>

</xsl:stylesheet>
