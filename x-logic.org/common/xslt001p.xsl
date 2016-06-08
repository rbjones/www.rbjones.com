<?xml version="1.0" encoding="iso-8859-1"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
				version="1.0"
                xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
				xmlns:xt="http://www.jclark.com/xt"
                extension-element-prefixes="xt">

<xsl:output method="xhtml" version="1.0" indent="no" omit-xml-declaration="yes" standalone="yes"/>

<xsl:include href="X-Logic.xsl"/>
<xsl:include href="frame01p.xsl"/>
<xsl:include href="IndexFramep.xsl"/>
<xsl:include href="MainFrame.xsl"/>
<xsl:include href="ppft.xsl"/>
<xsl:include href="xhtmlinxld.xsl"/>
<xsl:include href="sitespecific.xsl"/>

<xsl:template name="fsuffix">
  <xsl:text>html</xsl:text>
</xsl:template>

<xsl:template match="xld:xldoc">

  <xt:document href="{@name}.html" method="html">
	<xsl:call-template name="xldframe"/>
  </xt:document>

  <xt:document href="{@name}-i.html" method="html">
	<xsl:call-template name="xldindex"/>
  </xt:document>

  <xt:document href="{@name}-i.php" method="html">
	<xsl:call-template name="xldindexp"/>
  </xt:document>

  <xt:document href="{@name}-m.html" method="html">
	<xsl:call-template name="xldmain"/>
  </xt:document>

</xsl:template>

</xsl:stylesheet>











