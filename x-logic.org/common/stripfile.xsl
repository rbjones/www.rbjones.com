<?xml version="1.0" encoding="iso-8859-1"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
				version="1.0"
                xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
				xmlns:xt="http://www.jclark.com/xt"
                extension-element-prefixes="xt">

<xsl:output method="text" indent="no" omit-xml-declaration="yes"/>

<xsl:template match="xld:xldoc">

  <xsl:for-each select="xld:stripft">
    <xsl:variable name="lang">
      <xsl:value-of select="@lang"/>
    </xsl:variable>
    <xsl:variable name="suffix">
      <xsl:if test="@suffix"><xsl:value-of select="@suffix"/></xsl:if>
      <xsl:if test="not(@suffix)">
        <xsl:if test="substring-after($lang,'xl-')">
	      <xsl:value-of select="substring-after($lang,'xl-')"/>
	    </xsl:if>
        <xsl:if test="not(substring-after($lang,'xl-'))">
	      <xsl:value-of select="$lang"/>
	    </xsl:if>
	  </xsl:if>
    </xsl:variable> 
    <xsl:variable name="filename">
      <xsl:if test="@filename"><xsl:value-of select="@filename"/></xsl:if>
      <xsl:if test="not(@filename)">
        <xsl:value-of select="//xld:xldoc/@name"/>
        <xsl:text>.</xsl:text>
        <xsl:value-of select="$suffix"/>
      </xsl:if>
    </xsl:variable>
    <xt:document href="{$filename}" method="text">
      <xsl:for-each select="//xld:ft[@lang=$lang]">
        <xsl:sort select="@key"/>
     	<xsl:apply-templates/>
      </xsl:for-each>
    </xt:document>
  </xsl:for-each>

</xsl:template>

</xsl:stylesheet>











