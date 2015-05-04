<?xml version="1.0" encoding="iso-8859-1"?>

<!-- stylesheet for site specific templates 
     $Id: sitespecific.xsl,v 1.2 2006/03/25 22:50:36 rbj01 Exp $ -->

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
				version="1.0"
				xmlns="http://www.w3.org/TR/xhtml1/strict"
				xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
				xsl:exclude-result-prefixes="xld">

<xsl:template name="domain">
  <xsl:text>www.rbjones.com</xsl:text>
</xsl:template>

<xsl:template name="top">
  <xsl:text>index.htm</xsl:text>
</xsl:template>

</xsl:stylesheet>



