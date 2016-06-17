<?xml version="1.0" encoding="utf-8"?>

<!-- stylesheet for transforming xml xldoc into xhtml -->

<xsl:stylesheet
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="2.0"
  xmlns="http://www.w3.org/1999/xhtml"
  xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
  exclude-result-prefixes="xld">

<xsl:template mode="indexframe" match="xld:hide"/>

<xsl:template name="xldindex">
  <xsl:param name="class" tunnel="yes"/>
  <xsl:param name="title" />
  <xsl:call-template name="XHTML1Transitional"/>
<xsl:variable name="path" select="concat('file:',$root,$dir,$name)"/>
  <html>
  <xsl:call-template name="newline"/>
  <xsl:comment><xsl:value-of select="@id"/></xsl:comment>
  <xsl:call-template name="newline"/>
  <xsl:call-template name="shorthead">
      <xsl:with-param name="title" tunnel="yes"><xsl:value-of select="@title"/></xsl:with-param>
    </xsl:call-template>
  <body class="{$class}i">
  <xsl:call-template name="newline"/>
   <div class="{$class}ititle">
    <xsl:if test="xld:indextitle">
      <xsl:apply-templates select="xld:indextitle[position()=1]" mode="indextitle"/>
    </xsl:if>
	<xsl:if test="not(xld:indextitle)"><xsl:value-of select="@title"/></xsl:if>
   </div>
    <table class="{$class}i" cellspacing="2" align="center">
      <xsl:apply-templates mode="index"/>
    </table>
  <xsl:call-template name="newline"/>
  <div class="{$class}ifoot">
  <xsl:call-template name="newline"/>
  <a target="_top" href="{@up}"><img src="{$imagepath}/up.gif" alt="up" border="0" align="bottom"/></a>
  <xsl:call-template name="newline"/>
  <a target="_top" href="{concat($rootpath,$topindex)}"><img src="{$imagepath}/home.gif" alt="HOME" border="0" align="bottom"/></a>
  <xsl:call-template name="newline"/>
  <xsl:call-template name="author"/>
  <xsl:call-template name="newline"/>
  <xsl:call-template name="valid_xhtml10"/>
  <xsl:call-template name="newline"/>
  <p/>
  <xsl:call-template name="newline"/>
  <xsl:call-template name="google10"/>
  <xsl:call-template name="newline"/>
  </div>
  <xsl:call-template name="newline"/>
  </body>
  </html>
</xsl:template>

<xsl:template name="shorthead">
  <xsl:param name="title" />
  <head>
  <xsl:call-template name="newline"/>
  <link rel="STYLESHEET" type="text/css" href="{$rootpath}common/xl002.css" title="X-Logic style."/>
  <xsl:call-template name="newline"/>
  <title><xsl:value-of select="$title"/></title>
  </head>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="index" match="xld:maintitle">
</xsl:template>

<xsl:template mode="index" match="xld:indextitle">
</xsl:template>

<xsl:template mode="indextitle" match="xld:indextitle">
  <xsl:apply-templates/>
</xsl:template>

<xsl:template mode="index" match="xld:section">
  <xsl:param name="class" tunnel="yes"/>
  <xsl:param name="ititle">
      <xsl:if test="@ititle"><xsl:value-of select="@ititle"/></xsl:if>
      <xsl:if test="not(@ititle)"><xsl:value-of select="@title"/></xsl:if>
  </xsl:param>
  <xsl:param name="tag"><xsl:if test="not(@tag)"><xsl:value-of select="$ititle"/></xsl:if>
	                    <xsl:if test="@tag"><xsl:value-of select="@tag"/></xsl:if>
  </xsl:param>
  <xsl:if test="$tag!=''">
    <tr valign="top" align="center"><td class="{$class}i">
    <xsl:call-template name="newline"/>
    <a class="{$class}i" target="MainFrame" href="{$name}-m.{$suffix}#{$tag}"><xsl:value-of select="$ititle"/></a>
    <xsl:call-template name="newline"/>
    </td></tr>
  </xsl:if>
  <xsl:call-template name="newline"/>
</xsl:template>

</xsl:stylesheet>

