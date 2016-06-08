<?xml version="1.0" encoding="utf-8"?>

<!-- stylesheet for transforming xml xldoc into xhtml -->

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
				version="1.0"
				xmlns="http://www.w3.org/TR/xhtml1/strict"
				xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
				xsl:exclude-result-prefixes="xld">

<xsl:template match="*|/">
  <xsl:copy>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates/>
  </xsl:copy>
</xsl:template>

<xsl:template mode="mainframe" match="*|/">
  <xsl:copy>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates mode="mainframe"/>
  </xsl:copy>
</xsl:template>

<xsl:template match="xld:hide"/>

<xsl:template mode="mainframe" match="xld:hide"/>

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

<xsl:template name="xldmain">
  <xsl:variable name="prefix" select="''"/>
  <xsl:variable name="byreference" select="1>2"/>
  <xsl:call-template name="XHTML1Strict"/>
  <html>
  <xsl:call-template name="newline"/>
  <head>
  <xsl:call-template name="newline"/>
  <script language="JavaScript" src="{@root}common/style.js"><xsl:text> </xsl:text></script>
  <xsl:call-template name="newline"/>
  <script language="JavaScript">loadstylesheet("xl002","<xsl:value-of select='@root'/>common/")</script>
  <xsl:call-template name="newline"/>
  <title>MainFrame:<xsl:value-of select="@title"/></title>
  <xsl:call-template name="newline"/>
  </head>
  <xsl:call-template name="newline"/>
  <body class="m">
  <xsl:call-template name="newline"/>
  <div class="title">
    <xsl:if test="xld:maintitle[position()=1]">
      <xsl:apply-templates select="xld:maintitle" mode="maintitle"/>
    </xsl:if>
	<xsl:if test="not(xld:maintitle)"><xsl:value-of select="@title"/></xsl:if>
  </div>
    <xsl:apply-templates mode="mainframe">
	      <xsl:with-param name="prefix"><xsl:value-of select="$prefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
	</xsl:apply-templates>
  <xsl:call-template name="newline"/>
  <div class="foot">
  <xsl:call-template name="newline"/>
  <hr width="70%" />
  <xsl:call-template name="newline"/>
  <p>
  <xsl:call-template name="newline"/>
  <a target="_top" href="{@up}"><img src="{@root}images/up.gif" alt="up" border="0" align="bottom"/></a>
  <xsl:call-template name="newline"/>
  <a target="_top" href="{@root}index.html"><img src="{@root}images/home.gif" alt="quick index" border="0" align="bottom"/></a>
  <xsl:call-template name="newline"/>
  <xsl:call-template name="author"/>
  <xsl:call-template name="newline"/>
  </p>
  <xsl:call-template name="newline"/>
  <p><xsl:value-of select="@id"/></p>
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
  <title><xsl:value-of select="@title"/></title>
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
  <title><xsl:value-of select="@title"/></title>
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
  <title><xsl:value-of select="@title"/></title>
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

<xsl:template mode="mainframe" match="xld:section">
  <xsl:param name="prefix"/>
  <xsl:param name="byreference"/>
  <xsl:if test="not(@doc)">
       <xsl:call-template name="section">
	      <xsl:with-param name="prefix"><xsl:value-of select="$prefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
       </xsl:call-template>
  </xsl:if>
  <xsl:if test="@doc">
       <xsl:call-template name="refsection">
	      <xsl:with-param name="prefix"><xsl:value-of select="$prefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
       </xsl:call-template>
  </xsl:if>
</xsl:template>

<xsl:template mode="referenced" match="*|/">
  <xsl:copy>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates mode="referenced"/>
  </xsl:copy>
</xsl:template>

<xsl:template name="refsection">
  <xsl:param name="prefix"/>
  <xsl:param name="byreference"/>
  <xsl:variable name="srcsite">
    <xsl:call-template name="sitesrc"/>
  </xsl:variable>
  <xsl:variable name="newprefix">
	        <xsl:if test="@dir">
			  <xsl:value-of select="concat($prefix,@dir,'/')"/>
			</xsl:if>
	        <xsl:if test="not(@dir)"><xsl:value-of select="$prefix"/></xsl:if>
  </xsl:variable>
  <xsl:variable name="docpath">
	        <xsl:if test="@dir">
			  <xsl:value-of select="concat($srcsite,@dir,'/',@doc,'.xmlt')"/>
			</xsl:if>
	        <xsl:if test="not(@dir)"><xsl:value-of select="concat($srcsite,@doc,'.xmlt')"/></xsl:if>
  </xsl:variable> 
  <xsl:variable name="dochtmref">
			  <xsl:value-of select="concat($newprefix,@doc,'.html')"/>
  </xsl:variable> 
  <xsl:param name="ititle">
      <xsl:if test="@ititle"><xsl:value-of select="@ititle"/></xsl:if>
      <xsl:if test="not(@ititle)"><xsl:value-of select="@title"/></xsl:if>
  </xsl:param>
  <xsl:param name="tag"><xsl:if test="not(@tag)"><xsl:value-of select="$ititle"/></xsl:if>
	                    <xsl:if test="@tag"><xsl:value-of select="@tag"/></xsl:if>
  </xsl:param>
  <xsl:param name="title">
     <xsl:if test="not(@title)"><xsl:value-of select="@ititle"/></xsl:if>
	 <xsl:if test="@title"><xsl:value-of select="@title"/></xsl:if>
  </xsl:param>
  <xsl:if test="$tag!=''"><a><xsl:attribute name="name"><xsl:value-of select="$tag"/></xsl:attribute></a>
  </xsl:if>
  <xsl:call-template name="newline"/>
  <xsl:apply-templates select="document($docpath,@doc)//xld:section[position()=1]" mode="referenced">
	      <xsl:with-param name="prefix"><xsl:value-of select="$newprefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="true"/></xsl:with-param>
	      <xsl:with-param name="title"><xsl:value-of select="$title"/></xsl:with-param>
	      <xsl:with-param name="dochtmref"><xsl:value-of select="$dochtmref"/></xsl:with-param>
  </xsl:apply-templates>
</xsl:template>

<xsl:template mode="referenced" match="xld:section">
  <xsl:param name="prefix"/>
  <xsl:param name="byreference"/>
  <xsl:param name="title"/>
  <xsl:param name="dochtmref"/>
  <table class="sechead" width="100%">
  <tr valign="top">
  <xsl:call-template name="newline"/>
   <td width="200" class="sectitle">
     <a href="{$dochtmref}" target="_top" class="sectitleref"><xsl:value-of select="$title"/></a>
   </td>
  <xsl:call-template name="newline"/>
   <xsl:if test="xld:abstract">
     <td class="abstract">
       <table class="abstract" border="1" cellspacing="0"><tr><td class="abstract">
       <xsl:call-template name="newline"/>
       <xsl:apply-templates mode="abstract" select="xld:abstract"/>
       <xsl:call-template name="newline"/>
       </td></tr></table>
       <xsl:call-template name="newline"/>
     </td>
   </xsl:if>
  </tr></table>
  <xsl:call-template name="newline"/>
  <xsl:apply-templates mode="mainframe">
	      <xsl:with-param name="prefix"><xsl:value-of select="$prefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
  </xsl:apply-templates>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template name="section">
  <xsl:param name="prefix"/>
  <xsl:param name="byreference"/>
  <xsl:param name="ititle">
      <xsl:if test="@ititle"><xsl:value-of select="@ititle"/></xsl:if>
      <xsl:if test="not(@ititle)"><xsl:value-of select="@title"/></xsl:if>
  </xsl:param>
  <xsl:param name="tag"><xsl:if test="not(@tag)"><xsl:value-of select="$ititle"/></xsl:if>
	                    <xsl:if test="@tag"><xsl:value-of select="@tag"/></xsl:if>
  </xsl:param>
  <xsl:param name="title">
     <xsl:if test="not(@title)"><xsl:value-of select="@ititle"/></xsl:if>
	 <xsl:if test="@title"><xsl:value-of select="@title"/></xsl:if>
  </xsl:param>
  <xsl:if test="$tag!=''"><a><xsl:attribute name="name"><xsl:value-of select="$tag"/></xsl:attribute></a>
  </xsl:if>
  <xsl:call-template name="newline"/>
  <table class="sechead" width="100%">
  <tr valign="top">
  <xsl:call-template name="newline"/>
   <td width="200" class="sectitle">
   <xsl:if test="@href">
     <a target="_top" href="{@href}" class="sechead"><xsl:value-of select="$title"/></a>
   </xsl:if>
   <xsl:if test="not(@href)">
     <xsl:value-of select="$title"/>
   </xsl:if>
   </td>
  <xsl:call-template name="newline"/>
   <xsl:if test="xld:abstract">
     <td class="abstract">
       <table class="abstract" border="1" cellspacing="0"><tr><td class="abstract">
       <xsl:call-template name="newline"/>
       <xsl:apply-templates mode="abstract" select="xld:abstract"/>
       <xsl:call-template name="newline"/>
       </td></tr></table>
       <xsl:call-template name="newline"/>
     </td>
   </xsl:if>
  </tr></table>
  <xsl:call-template name="newline"/>
  <xsl:apply-templates mode="mainframe">
	      <xsl:with-param name="prefix"><xsl:value-of select="$prefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
  </xsl:apply-templates>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="abstract" match="xld:abstract">
    <xsl:apply-templates mode="mainframe"/>	
</xsl:template>

<xsl:template mode="mainframe" match="xld:abstract">
</xsl:template>

<xsl:template mode="mainframe" match="xld:indextitle">
</xsl:template>

<xsl:template mode="mainframe" match="xld:maintitle">
</xsl:template>

<xsl:template mode="maintitle" match="xld:maintitle">
  <xsl:apply-templates/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:secbody">
  <xsl:param name="prefix"/>
  <xsl:param name="byreference"/>
  <table class="secbody" width="100%" cellpadding="0" cellspacing="0">
  <xsl:if test="@title">
    <caption class="secbody"><xsl:value-of select="@title"/></caption>
  </xsl:if>
  <tr valign="top">
  <xsl:call-template name="newline"/>
  <xsl:variable name="cols" select="xld:sbcol"/>
  <xsl:variable name="numcols" select="count($cols)"/>
  <xsl:variable name="colwidth">
    <xsl:if test="$numcols=1">100%</xsl:if>
    <xsl:if test="$numcols=2">50%</xsl:if>
    <xsl:if test="$numcols=3">33%</xsl:if>
    <xsl:if test="$numcols=4">25%</xsl:if>
    <xsl:if test="$numcols=5">20%</xsl:if>
  </xsl:variable>
    <xsl:apply-templates mode="mainframe">
	      <xsl:with-param name="colwidth"><xsl:value-of select="$colwidth"/></xsl:with-param>
	      <xsl:with-param name="prefix"><xsl:value-of select="$prefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
    </xsl:apply-templates>
  <xsl:call-template name="newline"/>
  </tr></table>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:sbcol">
  <xsl:param name="colwidth"/>
  <xsl:param name="prefix"/>
  <xsl:param name="byreference"/>
  <td class="sbcol">
    <xsl:for-each select="@*">
	  <xsl:copy/>
    </xsl:for-each>
    <xsl:if test="not(@width)">
      <xsl:attribute name="width"><xsl:value-of select="$colwidth"/></xsl:attribute>
    </xsl:if>
  <table class="sbcol" cellpadding="5" width="100%">
  <xsl:call-template name="newline"/>
    <xsl:apply-templates mode="mainframe">
	      <xsl:with-param name="prefix"><xsl:value-of select="$prefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
    </xsl:apply-templates>
  <xsl:call-template name="newline"/>
  </table>
  </td>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:subsec">
  <xsl:param name="prefix"/>
  <xsl:param name="byreference"/>
  <tr><td class="subsec">
  <xsl:call-template name="newline"/>
  <xsl:if test="@title and not(@href) and not(@lhref)">
    <div class="ssectitle"><xsl:value-of select="@title"/></div>
  </xsl:if>
  <xsl:if test="@lhref">
    <a class="ssectitle" href="{@lhref}" target="MainFrame"><xsl:value-of select="@title"/></a>
  </xsl:if> 
  <xsl:if test="@href">
    <a class="ssectitle" href="{@href}" target="_top"><xsl:value-of select="@title"/></a>
  </xsl:if> 
  <xsl:call-template name="newline"/>
  <div class="subsec">
  <xsl:call-template name="newline"/>
    <xsl:apply-templates mode="mainframe">
	      <xsl:with-param name="prefix"><xsl:value-of select="$prefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
    </xsl:apply-templates>
  <xsl:call-template name="newline"/>
  </div>
  </td></tr>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:secref">
  <xsl:param name="prefix"/>
  <xsl:param name="byreference"/>
  <xsl:variable name="title"><xsl:value-of select="@title"/></xsl:variable>
  <xsl:variable name="rsec" select="//xld:section[@title=$title][position()=1]"/>
  <xsl:variable name="ititle">
      <xsl:if test="$rsec/@ititle"><xsl:value-of select="$rsec/@ititle"/></xsl:if>
      <xsl:if test="not($rsec/@ititle)"><xsl:value-of select="@title"/></xsl:if>
  </xsl:variable>
  <xsl:variable name="tag"><xsl:if test="not($rsec/@tag)"><xsl:value-of select="$ititle"/></xsl:if>
	                    <xsl:if test="$rsec/@tag"><xsl:value-of select="$rsec/@tag"/></xsl:if>
  </xsl:variable>
  <xsl:variable name="newprefix">
	        <xsl:if test="$rsec/@dir">
			  <xsl:value-of select="concat($prefix,$rsec/@dir,'/')"/>
			</xsl:if>
	        <xsl:if test="not($rsec/@dir)"><xsl:value-of select="$prefix"/></xsl:if>
  </xsl:variable> 
  <xsl:variable name="docref">
	        <xsl:if test="$rsec/@dir">
			  <xsl:value-of select="concat($rsec/@dir,'/',$rsec/@doc,'.xmlt')"/>
			</xsl:if>
	        <xsl:if test="not($rsec/@dir)"><xsl:value-of select="concat($rsec/@doc,'.xmlt')"/></xsl:if>
  </xsl:variable> 
  <xsl:variable name="dochtmref">
			  <xsl:value-of select="concat($newprefix,$rsec/@doc,'.html')"/>
  </xsl:variable> 
  <tr><td class="subsec">
  <xsl:call-template name="newline"/>
  <div class="secreftitle">
  <xsl:if test="$byreference = 'false'">
    <a href="#{$tag}" class="secreftitle"><xsl:value-of select="@title"/></a>
  </xsl:if>
  <xsl:if test="$byreference != 'false'">
    <xsl:if test="$rsec/@doc">    
      <a href="{$dochtmref}" target="_top" class="secreftitle"><xsl:value-of select="@title"/></a>
    </xsl:if>
    <xsl:if test="not($rsec/@doc)">    
      <xsl:value-of select="@title"/>
    </xsl:if>
  </xsl:if>
  </div>
  <xsl:call-template name="newline"/>
  <div class="subsec">
  <xsl:call-template name="newline"/>
  <xsl:if test="$rsec/xld:abstract">
    <xsl:apply-templates select="$rsec/xld:abstract" mode="refabstract">
	      <xsl:with-param name="prefix"><xsl:value-of select="$prefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
    </xsl:apply-templates>
  </xsl:if>
  <xsl:if test="not($rsec/xld:abstract)">
    <xsl:if test="$rsec/@doc">
      <xsl:apply-templates select="document($docref,$rsec/@doc)//xld:section[position()=1]/xld:abstract[position()=1]" mode="refabstract">
	      <xsl:with-param name="prefix"><xsl:value-of select="$newprefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
      </xsl:apply-templates>
    </xsl:if>
  </xsl:if>
  <xsl:call-template name="newline"/>
  </div>
  </td></tr>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:doctitle">
</xsl:template>

<xsl:template mode="refabstract" match="xld:abstract">
  <xsl:param name="prefix"/>
  <xsl:param name="byreference"/>
    <xsl:apply-templates mode="mainframe">
	      <xsl:with-param name="prefix"><xsl:value-of select="$prefix"/></xsl:with-param>
	      <xsl:with-param name="byreference"><xsl:value-of select="$byreference"/></xsl:with-param>
    </xsl:apply-templates>	
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
    <xsl:for-each select="@*[self::name]">
      <xsl:copy/>
    </xsl:for-each>
 </img>
</xsl:template>

<xsl:template mode="mainframe" match="xld:sg">
 <img src="{/xld:xldoc/@root}images/sg/{@name}">
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
  <xsl:text>&#xD;&#xA;</xsl:text>
</xsl:template>

<xsl:template match="copyright">
  <xsl:text disable-output-escaping="yes">&amp;copy;</xsl:text>
</xsl:template>

<xsl:template match="xld:slink">
 <xsl:param name="protocol">
  <xsl:if test="not(@protocol)"><xsl:text>http</xsl:text></xsl:if> 
  <xsl:if test="@protocol"><xsl:value-of select="@protocol"/></xsl:if> 
 </xsl:param>
 <xsl:param name="site">
  <xsl:if test="not(@domain)"><xsl:text></xsl:text></xsl:if> 
  <xsl:if test="@domain"><xsl:value-of select="$protocol"/>://<xsl:value-of select="@domain"/>/</xsl:if> 
 </xsl:param>
 <a>
    <xsl:attribute name="target">_top</xsl:attribute>
    <xsl:attribute name="href"><xsl:value-of select="$site"/><xsl:value-of select="@file"/></xsl:attribute>
    <xsl:for-each select="@*">
	  <xsl:copy/>
    </xsl:for-each>
 <xsl:apply-templates/>
 </a>
</xsl:template>

<xsl:template match="xld:xlink">
 <a>
    <xsl:attribute name="target">_top</xsl:attribute>
    <xsl:for-each select="@*">
	  <xsl:copy/>
    </xsl:for-each>
 <xsl:apply-templates/>
 </a>
</xsl:template>

</xsl:stylesheet>

