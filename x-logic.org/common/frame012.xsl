<?xml version="1.0" encoding="utf-8"?>

<xsl:stylesheet
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="2.0"
  xmlns="http://www.w3.org/1999/xhtml">

<xsl:template name="xldframe">

<xsl:call-template name="XHTML1Frameset"/>

<xsl:comment>created <xsl:value-of select="@created"/></xsl:comment>
<xsl:comment><xsl:value-of select="@id"/></xsl:comment>
<xsl:text>&#xA;</xsl:text>

<html>
<xsl:call-template name="framehead"/>

<frameset class="fr1" cols="*,180">
<frame src="{$mlfn}" name="MainFrame" />
<frame src="{$ilfn}" name="IndexFrame" />

<xsl:text>&#xA;</xsl:text>

<noframes>
<body>
<a href="{$mlfn}"><xsl:value-of select="@title"/></a> (for noframe browsers)
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
  <xsl:call-template name="newline"/>
  <meta name="description" content="{@description}" />
  <xsl:call-template name="newline"/>
  <meta name="keywords" content="RbJ FactasiA {@keywords}" />
  <xsl:call-template name="newline"/>
  <link rel="STYLESHEET" type="text/css" href="{$rootpath}common/xl002.css" title="X-Logic style."/>
  <xsl:call-template name="newline"/>
  </head>
</xsl:template>

</xsl:stylesheet>




