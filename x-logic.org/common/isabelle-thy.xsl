<?xml version="1.0" encoding="iso-8859-1"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
				version="1.0"
                xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
				xmlns:xt="http://www.jclark.com/xt"
                extension-element-prefixes="xt">

<xsl:output method="text" version="1.0" indent="no" omit-xml-declaration="yes" standalone="yes"/>

<xsl:template match="xld:xldoc">

  <xt:document href="{@theoryname}.thy" method="text">
	<xsl:apply-templates mode="copythy"/>
  </xt:document>

  <xt:document href="{@theoryname}.ML" method="text">
	<xsl:apply-templates mode="copyML"/>
  </xt:document>

</xsl:template>

<xsl:template match="xld:ft[@lang='xl-isabelle-thy']" mode="copythy">
    <xsl:apply-templates/>
</xsl:template>

<xsl:template match="*|/" mode="copythy">
    <xsl:apply-templates mode="copythy"/>
</xsl:template>

<xsl:template match="text()|@*" mode="copythy">
    <xsl:apply-templates mode="copythy"/>
</xsl:template>

<xsl:template match="xld:ft[@lang='xl-isabelle-ML']" mode="copyML">
    <xsl:apply-templates/>
</xsl:template>

<xsl:template match="*|/" mode="copyML">
    <xsl:apply-templates mode="copyML"/>
</xsl:template>

<xsl:template match="text()|@*" mode="copyML">
    <xsl:apply-templates mode="copyML"/>
</xsl:template>

</xsl:stylesheet>











