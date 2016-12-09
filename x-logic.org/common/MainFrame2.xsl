<?xml version="1.0" encoding="utf-8"?>

<!-- stylesheet for transforming xml xldoc into xhtml -->

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="2.0"
				xmlns="http://www.w3.org/1999/xhtml"
				xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
				exclude-result-prefixes="xld">

<!-- this is the catchall template copying any other elements in mainframe mode -->

<xsl:template mode="mainframe" match="*|/">
  <xsl:copy>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates mode="mainframe"/>
  </xsl:copy>
</xsl:template>

<!-- this is the main template which creates the html document for the "MainFrame" -->
<!-- also used for documents without frames -->

<xsl:template name="xldmain">
  <xsl:param name="class" tunnel="yes"/>
  <xsl:param name="title" />
  <xsl:variable name="prefix" select="''"/>
  <xsl:variable name="byreference" select="1>2"/>
  <xsl:call-template name="XHTML1Transitional"/>
  <html>
  <xsl:call-template name="newline"/>
  <head>
  <xsl:call-template name="newline"/>
  <link rel="STYLESHEET" type="text/css" href="{$rootpath}common/xl002.css" title="X-Logic style."/>
  <xsl:call-template name="newline"/>
  <title><xsl:value-of select="@title"/></title>
  </head>
  <xsl:call-template name="newline"/>
  <body class="{$class}m">
  <xsl:call-template name="newline"/>
  <xsl:choose>
   <xsl:when test="xld:maintitle[position()=1]/@align='center'">
    <center>
    <div class="{$class}title">
     <xsl:if test="xld:maintitle[position()=1]">
      <xsl:apply-templates select="xld:maintitle" mode="maintitle"/>
     </xsl:if>
	<xsl:if test="not(xld:maintitle)"><xsl:value-of select="@title"/></xsl:if>
    </div>
    </center>
   </xsl:when>
   <xsl:otherwise>
    <div class="{$class}title">
     <xsl:if test="xld:maintitle[position()=1]">
      <xsl:apply-templates select="xld:maintitle" mode="maintitle"/>
     </xsl:if>
	<xsl:if test="not(xld:maintitle)"><xsl:value-of select="@title"/></xsl:if>
    </div>
   </xsl:otherwise>
  </xsl:choose>
  <xsl:apply-templates mode="mainframe">
      <xsl:with-param name="prefix" tunnel="yes"><xsl:value-of select="$prefix"/></xsl:with-param>
      <xsl:with-param name="byreference" tunnel="yes"><xsl:value-of select="$byreference"/></xsl:with-param>
  </xsl:apply-templates>
  <xsl:call-template name="newline"/>
  <div class="{$class}foot"><xsl:call-template name="newline"/>
  <hr width="70%" /><xsl:call-template name="newline"/>
  <p><xsl:call-template name="newline"/>
  <a target="_top" href="{@up}">
     <img src="{$imagepath}/up.gif" alt="up" border="0" align="bottom"/>
  </a>
  <xsl:call-template name="newline"/>
  <a target="_top" href="{concat($rootpath,$topindex)}">
     <img src="{$imagepath}/home.gif" alt="quick index" border="0" align="bottom"/>
  </a>
  <xsl:call-template name="newline"/>
  <xsl:call-template name="author"/>
  <xsl:call-template name="newline"/>
  </p>
  <xsl:call-template name="newline"/>
  <xsl:call-template name="privacy"/>
  <xsl:call-template name="newline"/>
  <p>Created:<xsl:value-of select="@created"/></p>
  <xsl:call-template name="newline"/>
  <p><xsl:value-of select="@id"/></p>
  <xsl:call-template name="newline"/>
  <xsl:call-template name="valid_xhtml10"/>
  </div>
  </body>
  </html>
</xsl:template>

<!-- A section in a document may either be supplied with content or may -->
<!-- be a reference to some other document.  In the latter case there -->
<!-- is a "doc" attribute which names the document, and the content of -->
<!-- the section in this document will be a version of the first -->
<!-- section of the document referred to, which should always be a -->
<!-- suitable overview of that document.  The section template just -->
<!-- tests for the presence of the doc attribute and calls a different -->
<!-- named template according to whether the content is to be -->
<!-- retrieved from another document or not -->

<xsl:template mode="mainframe" match="xld:section">
  <xsl:if test="not(@doc)"><xsl:call-template name="section"/></xsl:if>
  <xsl:if test="@doc"><xsl:call-template name="refsection"/></xsl:if>
</xsl:template>

<!-- an un-referenced section -->

<xsl:template name="section">
  <xsl:param name="class" tunnel="yes"/>
  <xsl:param name="ititle">
      <xsl:if test="@ititle"><xsl:value-of select="@ititle"/></xsl:if>
      <xsl:if test="not(@ititle)"><xsl:value-of select="@title"/></xsl:if>
  </xsl:param>
  <xsl:param name="tag">
      <xsl:if test="not(@tag)"><xsl:value-of select="$ititle"/></xsl:if>
      <xsl:if test="@tag"><xsl:value-of select="@tag"/></xsl:if>
  </xsl:param>
  <xsl:param name="title">
      <xsl:if test="not(@title)"><xsl:value-of select="@ititle"/></xsl:if>
      <xsl:if test="@title"><xsl:value-of select="@title"/></xsl:if>
  </xsl:param>
  <xsl:if test="$tag!=''">
      <a><xsl:attribute name="name"><xsl:value-of select="$tag"/></xsl:attribute></a>
  </xsl:if>
  <xsl:call-template name="newline"/>
  <table class="{$class}sechead" width="100%">
  <tr valign="top">
  <xsl:call-template name="newline"/>
   <td width="200" class="{$class}sectitle">
   <xsl:if test="@href">
     <a target="_top" href="{@href}" class="{$class}sechead"><xsl:value-of select="$title"/></a>
   </xsl:if>
   <xsl:if test="not(@href)">
     <xsl:value-of select="$title"/>
   </xsl:if>
   </td>
  <xsl:call-template name="newline"/>
   <xsl:if test="xld:abstract">
     <td class="{$class}abstract">
       <table class="{$class}abstract" border="1" cellspacing="0"><tr><td class="{$class}abstract">
       <xsl:call-template name="newline"/>
       <xsl:apply-templates mode="abstract" select="xld:abstract"/>
       <xsl:call-template name="newline"/>
       </td></tr></table><xsl:call-template name="newline"/>
     </td>
   </xsl:if>
  </tr></table><xsl:call-template name="newline"/>
  <xsl:apply-templates mode="mainframe"/><xsl:call-template name="newline"/>
</xsl:template>

<!-- a section included by reference from the top of some other document. -->
<!-- The main differences are: (a) that the title of the section is -->
<!-- linked to the page referred to and (b) that the processing of the -->
<!-- content of the section is undertaken in "referenced" mode, which -->
<!-- affects how links in that section are processed. -->

<xsl:template name="refsection">
  <xsl:param name="prefix" tunnel="yes"/>
  <xsl:variable name="ititle">
      <xsl:if test="@ititle"><xsl:value-of select="@ititle"/></xsl:if>
      <xsl:if test="not(@ititle)"><xsl:value-of select="@title"/></xsl:if>
  </xsl:variable>
  <xsl:variable name="tag">
      <xsl:if test="not(@tag)"><xsl:value-of select="$ititle"/></xsl:if>
      <xsl:if test="@tag"><xsl:value-of select="@tag"/></xsl:if>
  </xsl:variable>
  <xsl:variable name="title">
      <xsl:if test="not(@title)"><xsl:value-of select="@ititle"/></xsl:if>
      <xsl:if test="@title"><xsl:value-of select="@title"/></xsl:if>
  </xsl:variable>
  <xsl:variable name="srcsite">
    <xsl:call-template name="sitesrc"/>
  </xsl:variable>
  <xsl:variable name="newprefix">
      <xsl:if test="@dir"><xsl:value-of select="concat($prefix,@dir,'/')"/></xsl:if>
      <xsl:if test="not(@dir)"><xsl:value-of select="$prefix"/></xsl:if>
  </xsl:variable>
  <xsl:variable name="docpath">
      <xsl:if test="@dir"><xsl:value-of select="concat($srcsite,@dir,'/',@doc,'.xmlt')"/></xsl:if>
      <xsl:if test="not(@dir)"><xsl:value-of select="concat($srcsite,@doc,'.xmlt')"/></xsl:if>
  </xsl:variable> 
  <xsl:variable name="filename">
      <xsl:if test="@suf"><xsl:value-of select="concat($newprefix,@doc,'.',@suf)"/></xsl:if>
      <xsl:if test="not(@suf)"><xsl:value-of select="concat($newprefix,@doc,'.html')"/></xsl:if>
  </xsl:variable>
  <xsl:if test="$tag!=''">
      <a><xsl:attribute name="name"><xsl:value-of select="$tag"/></xsl:attribute></a>
  </xsl:if>
  <xsl:call-template name="newline"/>
  <xsl:comment><xsl:value-of select="document($docpath,@doc)//xld:xldoc/@id"/></xsl:comment>
  <xsl:message><xsl:value-of select="concat('***[2] ', $docpath)"/></xsl:message>
  <xsl:apply-templates select="document($docpath,@doc)//xld:section[position()=1]" mode="referenced">
      <xsl:with-param name="prefix" tunnel="yes"><xsl:value-of select="$newprefix"/></xsl:with-param>
      <xsl:with-param name="byreference" tunnel="yes"><xsl:value-of select="child::true"/></xsl:with-param>
      <xsl:with-param name="title"><xsl:value-of select="$title"/></xsl:with-param>
      <xsl:with-param name="dochtmref"><xsl:value-of select="$filename"/></xsl:with-param>
  </xsl:apply-templates>
</xsl:template>

<!-- mode "referenced" is used for material extracted from a document -->
<!-- referred to by the primary source document. -->

<!-- This template catches and flags elements processed in referenced mode -->
<!-- for which no specific rule is available -->

<xsl:template mode="referenced" match="*|/">
  <xsl:copy>
    <xsl:for-each select="@*"><xsl:copy/></xsl:for-each>
    <xsl:apply-templates mode="referenced"/>
  </xsl:copy>
</xsl:template>

<xsl:template mode="referenced" match="xld:section">
  <xsl:param name="class" tunnel="yes"/>
  <xsl:param name="title"/>
  <xsl:param name="dochtmref"/>
  <table class="{$class}sechead" width="100%">
  <tr valign="top"><xsl:call-template name="newline"/>
   <td width="200" class="{$class}sectitle">
     <a href="{$dochtmref}" target="_top" class="{$class}sectitleref"><xsl:value-of select="$title"/></a>
   </td>
  <xsl:call-template name="newline"/>
   <xsl:if test="xld:abstract">
     <td class="{$class}abstract">
       <table class="{$class}abstract" border="1" cellspacing="0"><tr><td class="{$class}abstract">
       <xsl:call-template name="newline"/>
       <xsl:apply-templates mode="refabstract" select="xld:abstract"/>
       <xsl:call-template name="newline"/>
       </td></tr></table><xsl:call-template name="newline"/>
     </td>
   </xsl:if>
  </tr></table>
  <xsl:call-template name="newline"/>
  <xsl:apply-templates mode="mainframe"/>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="abstract" match="xld:abstract"><xsl:apply-templates mode="mainframe"/></xsl:template>

<xsl:template mode="refabstract" match="xld:abstract"><xsl:apply-templates mode="referenced"/></xsl:template>

<xsl:template mode="mainframe" match="xld:abstract"></xsl:template>

<xsl:template mode="mainframe" match="xld:indextitle"></xsl:template>

<xsl:template mode="mainframe" match="xld:maintitle"></xsl:template>

<xsl:template mode="maintitle" match="xld:maintitle">
  <xsl:apply-templates mode="mainframe"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:secbody">
  <xsl:param name="class" tunnel="yes"/>
  <table class="{$class}secbody" width="100%" cellpadding="0" cellspacing="0">
  <xsl:if test="@title">
    <caption class="{$class}secbody"><xsl:value-of select="@title"/></caption>
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
    </xsl:apply-templates>
  <xsl:call-template name="newline"/>
  </tr></table>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:sbcol">
  <xsl:param name="class" tunnel="yes"/>
  <xsl:param name="colwidth"/>
  <td class="{$class}sbcol">
    <xsl:for-each select="@*"><xsl:copy/></xsl:for-each>
    <xsl:if test="not(@width)">
      <xsl:attribute name="width"><xsl:value-of select="$colwidth"/></xsl:attribute>
    </xsl:if>
  <table class="{$class}sbcol" cellpadding="5" width="100%">
    <xsl:if test="@title">
    <caption class="{$class}sbcol"><xsl:value-of select="@title"/></caption>
    </xsl:if>
  <xsl:call-template name="newline"/>
  <xsl:apply-templates mode="mainframe"/>
  <xsl:call-template name="newline"/>
  </table>
  </td>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:subsec">
  <xsl:if test="not(@doc)"><xsl:call-template name="subsec"/></xsl:if>
  <xsl:if test="@doc"><xsl:call-template name="subsecdoc"/></xsl:if>
</xsl:template>

<xsl:template name="subsec">
  <xsl:param name="class" tunnel="yes"/>
  <tr><td class="{$class}subsec"><xsl:call-template name="newline"/>
  <xsl:if test="@title and not(@href) and not(@lhref)">
    <div class="{$class}ssectitle"><xsl:value-of select="@title"/></div>
  </xsl:if>
  <xsl:if test="@lhref">
    <div class="{$class}secreftitle">
        <a class="{$class}ssectitle" href="{@lhref}" target="MainFrame"><xsl:value-of select="@title"/></a>
    </div>
  </xsl:if> 
  <xsl:if test="@href">
    <div class="{$class}secreftitle">
         <a class="{$class}ssectitle" href="{@href}" target="_top"><xsl:value-of select="@title"/>
	 </a>
    </div>
  </xsl:if><xsl:call-template name="newline"/>
  <div class="{$class}subsec"><xsl:call-template name="newline"/>
  <xsl:apply-templates mode="mainframe"/><xsl:call-template name="newline"/>
  </div></td></tr><xsl:call-template name="newline"/>
</xsl:template>

<xsl:template name="subsecdoc">
  <xsl:param name="class" tunnel="yes"/>
  <xsl:param name="prefix" tunnel="yes"/>
  <xsl:variable name="newprefix">
      <xsl:if test="@dir"><xsl:value-of select="concat($prefix,@dir,'/')"/></xsl:if>
      <xsl:if test="not(@dir)"><xsl:value-of select="$prefix"/></xsl:if>
  </xsl:variable>
  <xsl:variable name="filename">
      <xsl:if test="@suf"><xsl:value-of select="concat($newprefix,@doc,'.',@suf)"/></xsl:if>
      <xsl:if test="not(@suf)"><xsl:value-of select="concat($newprefix,@doc,'.html')"/></xsl:if>
  </xsl:variable>
  <tr><td class="{$class}subsec"><xsl:call-template name="newline"/>
    <div class="{$class}secreftitle">
         <a class="{$class}ssectitle" href="{$filename}" target="_top"><xsl:value-of select="@title"/>
	 </a>
    </div>
  <xsl:call-template name="newline"/>
  <div class="{$class}subsec"><xsl:call-template name="newline"/>
  <xsl:apply-templates mode="mainframe"/><xsl:call-template name="newline"/>
  </div></td></tr><xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:secref">
  <xsl:call-template name="secrefm">
    <xsl:with-param name="titlepos">
      <xsl:text></xsl:text>
    </xsl:with-param>
  </xsl:call-template>
</xsl:template>

<xsl:template mode="mainframe" match="xld:lsecref">
  <xsl:call-template name="secrefm">
    <xsl:with-param name="titlepos">
      <xsl:text>l</xsl:text>
    </xsl:with-param>
  </xsl:call-template>
</xsl:template>

<xsl:template name="secrefm">
  <xsl:param name="titlepos"/>
  <xsl:param name="class" tunnel="yes"/>
  <xsl:param name="prefix" tunnel="yes"/>
  <xsl:param name="byreference" tunnel="yes"/>
  <xsl:variable name="title"><xsl:value-of select="@title"/></xsl:variable>
  <xsl:variable name="rsec" select="//xld:section[@title=$title][position()=1]"/>
  <xsl:variable name="ititle">
    <xsl:if test="$rsec/@ititle"><xsl:value-of select="$rsec/@ititle"/></xsl:if>
    <xsl:if test="not($rsec/@ititle)"><xsl:value-of select="@title"/></xsl:if>
  </xsl:variable>
  <xsl:variable name="tag">
    <xsl:if test="not($rsec/@tag)"><xsl:value-of select="$ititle"/></xsl:if>
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
      <xsl:if test="@suf"><xsl:value-of select="concat($newprefix,$rsec/@doc,'.',@suf)"/></xsl:if>
      <xsl:if test="not(@suf)"><xsl:value-of select="concat($newprefix,$rsec/@doc,'.html')"/></xsl:if>
  </xsl:variable> 
  <tr><td class="{$class}subsec">
  <xsl:call-template name="newline"/>
  <div class="{$class}secref{$titlepos}title">
  <xsl:if test="$byreference = 'false'">
    <a href="#{$tag}" class="{$class}secref{$titlepos}title"><xsl:value-of select="@title"/></a>
  </xsl:if>
  <xsl:if test="$byreference != 'false'">
    <xsl:if test="$rsec/@doc">    
      <a href="{$dochtmref}" target="_top" class="{$class}secref{$titlepos}title"><xsl:value-of select="@title"/></a>
    </xsl:if>
    <xsl:if test="not($rsec/@doc)">    
      <xsl:value-of select="@title"/>
    </xsl:if>
  </xsl:if>
  </div>
  <xsl:call-template name="newline"/>
  <div class="{$class}subsec">
  <xsl:call-template name="newline"/>
  <xsl:choose>
   <xsl:when test="xld:abstract">
    <xsl:apply-templates select="xld:abstract" mode="refabstract"/>
   </xsl:when>
   <xsl:when test="$rsec/xld:abstract">
    <xsl:apply-templates select="$rsec/xld:abstract" mode="refabstract"/>
   </xsl:when>
   <xsl:when test="$rsec/@doc">
      <xsl:comment>
       <xsl:value-of select="document($docref,$rsec/@doc)//xld:xldoc/@id"/>
      </xsl:comment>
      <xsl:message><xsl:value-of select="concat('***[3] ', $docref)"/></xsl:message>
      <xsl:apply-templates
         select="document($docref,$rsec/@doc)//xld:section[position()=1]/xld:abstract[position()=1]"
	 mode="refabstract">
	 <xsl:with-param name="prefix" tunnel="yes"><xsl:value-of select="$newprefix"/></xsl:with-param>
      </xsl:apply-templates>
   </xsl:when>
  </xsl:choose>
  <xsl:call-template name="newline"/>
  </div>
  </td></tr>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:doctitle"></xsl:template>

<!-- this template processes references to symbol gifs (using for -->
<!-- characters not usually rendered correctly by browsers). -->

<xsl:template mode="#all" match="xld:sg">
 <img src="{$imagepath}sg/{@name}" alt="{@name}">
    <xsl:for-each select="@* except @name"><xsl:copy/>
    </xsl:for-each>
 </img>
</xsl:template>

<!-- image references in mainframe mode -->

<xsl:template match="xld:image" mode="#all">
 <img src="{concat($imagepath,@name)}">
    <xsl:for-each select="@* except @name">
      <xsl:copy/>
    </xsl:for-each>
 </img>
</xsl:template>

<xsl:template match="xld:sup" mode="#all">
 <sup>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
  <xsl:apply-templates mode="mainframe"/>	    
 </sup>
</xsl:template>

<xsl:template match="xld:sub" mode="#all">
 <sub>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
  <xsl:apply-templates mode="mainframe"/>	    
 </sub>
</xsl:template>

<!-- this template processes links to related sites, e.g. a link -->
<!-- between rbjones.com and x-logic.org -->

<xsl:template mode="#all" match="xld:slink">
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
    <xsl:for-each select="@*"><xsl:copy/></xsl:for-each>
    <xsl:apply-templates/>
 </a>
</xsl:template>

<!-- this template processes external hyperlinks -->

<xsl:template mode="#all" match="xld:xlink">
  <a>
    <xsl:attribute name="target">_top</xsl:attribute>
    <xsl:for-each select="@*"><xsl:copy/></xsl:for-each>
    <xsl:apply-templates/>
  </a>
</xsl:template>

<!-- this template processes reference to the bibliography -->

<xsl:template mode="#all" match="xld:bibref">
  <xsl:variable name="firstletter"><xsl:value-of select="substring(@name,1,1)"/></xsl:variable> 
  <xsl:variable name="rest"><xsl:value-of select="substring(@name,2)"/></xsl:variable> 
  <xsl:variable name="lcfirstletter">
    <xsl:value-of select="translate($firstletter,
      'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz')"/>
  </xsl:variable> 
  <xsl:variable name="ucfirstletter">
    <xsl:value-of select="translate($firstletter,
      'abcdefghijklmnopqrstuvwxyz','ABCDEFGHIJKLMNOPQRSTUVWXYZ')"/>
  </xsl:variable>
  <xsl:variable name="refname">
    <xsl:value-of select="concat($lcfirstletter,'.htm#',$ucfirstletter,$rest)"/>
  </xsl:variable>
 <a href="{$rootpath}rbjpub/philos/bibliog/{$refname}"
    target="_top">
 <i><xsl:value-of select="@name"/></i>
 </a>
</xsl:template>

<!-- this template processes reference to the glossary -->

<xsl:template mode="#all" match="xld:gloss">
  <xsl:variable name="firstletter"><xsl:value-of select="substring(@name,1,1)"/></xsl:variable> 
  <xsl:variable name="rest"><xsl:value-of select="substring(@name,2)"/></xsl:variable> 
  <xsl:variable name="lcfirstletter">
    <xsl:value-of select="translate($firstletter,
      'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz')"/>
  </xsl:variable> 
  <xsl:variable name="ucfirstletter">
    <xsl:value-of select="translate($firstletter,
      'abcdefghijklmnopqrstuvwxyz','ABCDEFGHIJKLMNOPQRSTUVWXYZ')"/>
  </xsl:variable>
  <xsl:variable name="glossname">
    <xsl:value-of select="concat($lcfirstletter,'.htm#',$ucfirstletter,$rest)"/>
  </xsl:variable>
 <a href="{$rootpath}rbjpub/philos/glossary/{$glossname}" target="_top">
 <i><xsl:value-of select="@name"/></i>
 </a>
</xsl:template>

</xsl:stylesheet>
