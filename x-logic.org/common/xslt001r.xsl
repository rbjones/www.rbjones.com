<?xml version="1.0" encoding="iso-8859-1"?>

<xsl:stylesheet
 xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.1"
 xmlns:xt="http://icl.com/saxon"
 xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
 xt:trace="no"
 extension-element-prefixes="xt">

<xsl:output method="html" version="1.0" indent="no" omit-xml-declaration="yes" standalone="yes"/>

<xsl:include href="X-Logic.xsl"/>
<xsl:include href="frame01.xsl"/>
<xsl:include href="IndexFrame.xsl"/>
<xsl:include href="MainFrame.xsl"/>
<xsl:include href="ppft.xsl"/>
<xsl:include href="xhtmlinxld.xsl"/>

<xsl:template match="xld:xldoc">
  <xsl:variable name="filename">
	        <xsl:if test="@suf">
			  <xsl:value-of select="concat(@name,'.',@suf)"/>
		</xsl:if>
	        <xsl:if test="not(@suf)"><xsl:value-of select="concat(@name,'.html')"/></xsl:if>
  </xsl:variable>

  <xsl:document href="{@name}-i.html">
	<xsl:call-template name="xldindex"/>
  </xsl:document>

  <xsl:document href="{@name}-m.html">
	<xsl:call-template name="xldmain"/>
  </xsl:document>

  <xsl:document href="{@name}.html">
  <xsl:call-template name="xldframe"/>
  </xsl:document>

</xsl:template>

</xsl:stylesheet>











