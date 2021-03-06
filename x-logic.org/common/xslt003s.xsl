<?xml version="1.0" encoding="iso-8859-1"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.1"
		xmlns="http://www.w3.org/TR/xhtml1/strict"
                xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
		xmlns:saxon="http://icl.com/saxon"
                extension-element-prefixes="saxon">

<xsl:output method="html" version="1.0" indent="no"/>

<xsl:include href="X-Logic.xsl"/>
<xsl:include href="IndexFrame.xsl"/>

<xsl:template match="xlpage">

  <saxon:output file="{@name}.html" method="html">
    <html>
	<xsl:call-template name="fullhead1"/>
	    <xsl:apply-templates/>
	</html>
  </saxon:output>

</xsl:template>

<xsl:template match="xld:huge-logo">
  <span class="huge-logo"><xsl:apply-templates/></span>   
</xsl:template>

</xsl:stylesheet>


















