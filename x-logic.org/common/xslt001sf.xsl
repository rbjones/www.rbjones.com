<?xml version="1.0" encoding="iso-8859-1"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="2.0"
                xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
		xmlns:saxon="http://icl.com/saxon"
                extension-element-prefixes="saxon">

<xsl:output method="xhtml" version="1.0" indent="yes"/>

<xsl:include href="Common2.xsl"/>
<xsl:include href="X-Logic.xsl"/>
<xsl:include href="frame012.xsl"/>
<xsl:include href="ppft.xsl"/>
<xsl:include href="xhtmlinxld.xsl"/>

<xsl:template match="xld:xldoc">
<xsl:call-template name="xldframe"/>
</xsl:template>

</xsl:stylesheet>











