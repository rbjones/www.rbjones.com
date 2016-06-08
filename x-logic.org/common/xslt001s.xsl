<?xml version="1.0" encoding="iso-8859-1"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.1"
                xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
		xmlns:saxon="http://icl.com/saxon"
                extension-element-prefixes="saxon">

<xsl:output method="xml" version="1.0" indent="yes" omit-xml-declaration="yes" standalone="yes"/>

<xsl:include href="X-Logic.xsl"/>
<xsl:include href="frame01.xsl"/>
<xsl:include href="IndexFrame.xsl"/>
<xsl:include href="MainFrame.xsl"/>
<xsl:include href="ppft.xsl"/>
<xsl:include href="xhtmlinxld.xsl"/>

<xsl:template match="xld:xldoc">

  <xsl:document href="{@name}.html" method="html">
	<xsl:call-template name="xldframe"/>
  </xsl:document>

  <xsl:document href="{@name}-i.html" method="html">
	<xsl:call-template name="xldindex"/>
  </xsl:document>

  <xsl:document href="{@name}-m.html" method="html">
	<xsl:call-template name="xldmain"/>
  </xsl:document>

</xsl:template>

</xsl:stylesheet>











