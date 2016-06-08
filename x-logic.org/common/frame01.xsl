<?xml version="1.0" encoding="utf-8"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
				version="1.0"
				xmlns="http://www.w3.org/TR/xhtml1/frameset">

<xsl:template name="xldframe">

<xsl:call-template name="XHTML1Frameset"/>
<html>
<xsl:call-template name="framehead"/>

<frameset cols="*,180" border="0">
<frame src="{@name}-m.html" name="MainFrame" />
<frame src="{@name}-i.html" name="IndexFrame" />

<xsl:text>&#xA;</xsl:text>
<xsl:comment>created <xsl:value-of select="@created"/> modified <xsl:value-of select="@modified"/>
<xsl:text>&#xA;</xsl:text>
<xsl:value-of select="@id"/>
</xsl:comment>
<xsl:text>&#xA;</xsl:text>

<noframes>
<body>
<a href="{@name}-m.html"><xsl:value-of select="@title"/></a> (for noframe browsers)
</body>
</noframes>
</frameset>
</html>
</xsl:template>

<xsl:template name="XHTML1Frameset">
  <xsl:text disable-output-escaping="yes">&lt;!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Frameset//EN"
               "http://www.w3.org/TR/xhtml1/DTD/frameset.dtd"&gt;</xsl:text>
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template name="framehead">
  <head>
  <title><xsl:value-of select="@title"/></title>
  <meta name="description" content="{@description}" />
  <meta name="keywords" content="RbJ FactasiA {@keywords}" />
  </head>
</xsl:template>

</xsl:stylesheet>




