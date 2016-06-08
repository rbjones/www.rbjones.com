<?xml version="1.0" encoding="iso-8859-1"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="2.0"
                xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
		xmlns:saxon="http://icl.com/saxon"
                extension-element-prefixes="saxon">

<!-- this is the style sheet for non-frame documents -->

<!-- parameter "root" must be set from the command line: it represents -->
<!-- the absolute location in the build tree of the root directory -->
<xsl:param name="root">/home/rbj/rbjones.com/build/</xsl:param>
<!-- parameter "dir" must be set from the command line: it represents the output file directory -->
<xsl:param name="dir">rbjpub/</xsl:param>
<!-- parameter "name" must be set from the command line: it represents the output file base name -->
<xsl:param name="name">file</xsl:param>
<!-- parameter "suffix" must be set from the command line: it represents the output file suffix -->
<xsl:param name="suffix">html</xsl:param>
<!-- parameter "imagedir" may be set from the command line: it -->
<!-- represents the image directory path -->
<xsl:param name="imagedir">images</xsl:param>
<xsl:variable name="path" select="concat('file:',$root,$dir)"/>
<xsl:variable name="rootpath" select="replace($dir, '[^/]+','..')"/>
<xsl:variable name="imagepath" select="concat($rootpath,$imagedir,'/')"/>
<xsl:variable name="mlfn" select="concat($name,'.',$suffix)"/>
<xsl:variable name="mfn" select="concat($path,$mlfn)"/>
<xsl:variable name="topindex">
  <xsl:if test="@topindex"><xsl:value-of select="@top"/></xsl:if>
  <xsl:if test="not(@topindex)"><xsl:value-of select="'rbjpub/index.htm'"/></xsl:if>
</xsl:variable>

<xsl:output name="main" method="xhtml" version="1.0" encoding="US-ASCII"/>

<xsl:include href="Common2.xsl"/>
<xsl:include href="X-Logic2.xsl"/>
<xsl:include href="MainFrame2.xsl"/>
<xsl:include href="ppft2.xsl"/>
<xsl:include href="xhtmlinxld.xsl"/>

<xsl:template match="xld:xldoc">

 <xsl:variable name="class">
   <xsl:choose>
     <xsl:when test="not(compare(@class,'con'))"><xsl:value-of select="''"/></xsl:when>
     <xsl:when test="not(@class)"><xsl:value-of select="''"/></xsl:when>
     <xsl:when test="@class"><xsl:value-of select="@class"/></xsl:when>
   </xsl:choose>
 </xsl:variable>

 <xsl:result-document href="{$mfn}" format="main">
 	<xsl:call-template name="xldmain">
	<xsl:with-param name="class" tunnel="yes"><xsl:value-of select="$class"/></xsl:with-param>
	<xsl:with-param name="title"><xsl:value-of select="@title"/></xsl:with-param>
	</xsl:call-template>
 </xsl:result-document>

</xsl:template>
</xsl:stylesheet>
