<?xml version="1.0" encoding="utf-8"?>

<!-- stylesheet for transforming xml xldoc into xhtml -->

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
				version="1.0"
				xmlns="http://www.w3.org/TR/xhtml1/strict"
				xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
				exclude-result-prefixes="xld">

<xsl:template match="*|/">
  <xsl:copy>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates/>
  </xsl:copy>
</xsl:template>

<xsl:template match="xld:hide"/>

<xsl:template mode="indexframe" match="xld:hide"/>

<xsl:template name="xldindex">
  <xsl:call-template name="XHTML1Strict"/>
  <html>
  <xsl:call-template name="newline"/>
  <xsl:call-template name="shorthead"/>
  <body class="i">
  <xsl:call-template name="newline"/>
   <div class="ititle">
    <xsl:if test="xld:indextitle">
      <xsl:apply-templates select="xld:indextitle[position()=1]" mode="indextitle"/>
    </xsl:if>
	<xsl:if test="not(xld:indextitle)"><xsl:value-of select="@title"/></xsl:if>
   </div>
    <table class="i" cellspacing="1" align="center">
      <xsl:apply-templates mode="index"/>
    </table>
  <xsl:call-template name="newline"/>
  <div class="ifoot">
  <xsl:call-template name="newline"/>
  <a target="_top" href="{@up}"><img src="{@root}images/up.gif" alt="up" border="0" align="bottom"/></a>
  <xsl:call-template name="newline"/>
  <a target="_top" href="{@root}index.html"><img src="{@root}images/home.gif" alt="HOME" border="0" align="bottom"/></a>
  <xsl:call-template name="newline"/>
  <xsl:call-template name="author"/>
  <xsl:call-template name="newline"/>
  </div>
  </body>
  </html>
</xsl:template>

<xsl:template name="fullhead1">
  <head>
  <xsl:call-template name="newline"/>
  <link rel="STYLESHEET" type="text/css" href="{@root}common/xl001.css" title="X-Logic"/>
  <xsl:call-template name="newline"/>
  <title>IndexFrame: <xsl:value-of select="@title"/></title>
  <xsl:call-template name="newline"/>
  <meta name="description" content="{@description}" />
  <xsl:call-template name="newline"/>
  <meta name="keywords" content="RbJ FactasiA {@keywords}" />
  <xsl:call-template name="newline"/>
  </head>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template name="fullhead">
  <head>
  <xsl:call-template name="newline"/>
  <link rel="STYLESHEET" type="text/css" href="{@root}common/xl002.css" title="X-Logic"/>
  <xsl:call-template name="newline"/>
  <title>IndexFrame: <xsl:value-of select="@title"/></title>
  <xsl:call-template name="newline"/>
  <meta name="description" content="{@description}" />
  <xsl:call-template name="newline"/>
  <meta name="keywords" content="RbJ FactasiA {@keywords}" />
  <xsl:call-template name="newline"/>
  </head>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template name="shorthead">
  <head>
  <xsl:call-template name="newline"/>
  <script language="JavaScript" src="{@root}common/style.js"><xsl:text> </xsl:text></script>
  <script language="JavaScript">loadstylesheet("xl002","<xsl:value-of select='@root'/>common/")</script>
  <xsl:call-template name="newline"/>
  <title>IndexFrame: <xsl:value-of select="@title"/></title>
  <xsl:call-template name="newline"/>
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
  <xsl:param name="ititle">
      <xsl:if test="@ititle"><xsl:value-of select="@ititle"/></xsl:if>
      <xsl:if test="not(@ititle)"><xsl:value-of select="@title"/></xsl:if>
  </xsl:param>
  <xsl:param name="tag"><xsl:if test="not(@tag)"><xsl:value-of select="$ititle"/></xsl:if>
	                    <xsl:if test="@tag"><xsl:value-of select="@tag"/></xsl:if>
  </xsl:param>
  <xsl:if test="$tag!=''">
    <tr valign="top" align="center"><td class="i">
    <xsl:call-template name="newline"/>
    <a class="i" target="MainFrame" href="{ancestor::xld:*/attribute::name}-m.html#{$tag}"><xsl:value-of select="$ititle"/></a>
    <xsl:call-template name="newline"/>
    </td></tr>
  </xsl:if>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template match="xld:img">
 <img src="{/xld:xldoc/@root}images/{@name}">
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
 </img>
</xsl:template>

<xsl:template match="xld:image">
 <img src="{/xld:xldoc/@root}images/{@name}">
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
 </img>
</xsl:template>

<xsl:template name="XHTML1Strict">
  <xsl:text disable-output-escaping="yes">&lt;!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
               "http://www.w3.org/TR/xhtml1/DTD/strict.dtd"&gt;</xsl:text>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template name="newline">
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template match="copyright">
  <xsl:text disable-output-escaping="yes">&amp;copy;</xsl:text>
</xsl:template>

</xsl:stylesheet>

