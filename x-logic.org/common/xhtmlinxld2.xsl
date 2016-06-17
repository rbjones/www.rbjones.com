<?xml version="1.0" encoding="iso-8859-1"?>

<!-- stylesheet allowing inclusion of xhtml tags in xld documents -->
<!--
In an xld document xhtml tags can be used and are copied into the result document.
However, unless they are identified as xhtml elements then they will arrive in the destination
xhtml with an xmlns attribute which shows that they belong to the xld namespace.
This doesn't seem to make any difference in the browsers I have tried, but one day xhtml aware
browsers will arrive and will realise that they don't understand them.
You can fix this just by prefixing the element name with "xhtml:" in your source document, but
that is a pain, so for some selected tags I provide a translation from "xld:tag" to "xhtml:tag".
Which is what this stylesheet is for.  There probably is a better way to do this.
-->

<xsl:stylesheet
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0"
  xmlns="http://www.w3.org/1999/xhtml"
  xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
  exclude-result-prefixes="xld">

<xsl:template mode="#all" match="xld:a">
 <a>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates/>
 </a>
</xsl:template>

<xsl:template mode="#all" match="xld:blockquote">
 <blockquote>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates/>
 </blockquote>
</xsl:template>

<xsl:template mode="#all" match="xld:br">
  <br/>
</xsl:template>

<xsl:template mode="#all" match="xld:center">
 <center>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates/>
 </center>
</xsl:template>

<xsl:template mode="#all" match="xld:h2">
 <h2>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates/>
 </h2>
</xsl:template>

<xsl:template mode="#all" match="xld:div">
 <h2>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates/>
 </h2>
</xsl:template>

<xsl:template mode="#all" match="xld:i">
 <i>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
    <xsl:apply-templates/>
 </i>
</xsl:template>

<xsl:template match="xld:img" mode="#all">
 <img src="{concat($imagepath,@name)}">
    <xsl:for-each select="@* except @name">
      <xsl:copy/>
    </xsl:for-each>
 </img>
</xsl:template>

<xsl:template mode="#all" match="xld:li">
  <li>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
  <xsl:apply-templates/>
  </li>
</xsl:template>

<xsl:template mode="#all" match="xld:ol">
  <ol>
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
  <xsl:apply-templates/>
  </ol>
</xsl:template>

<xsl:template mode="#all" match="xld:p">
  <p>
  <xsl:apply-templates/>
  </p>
</xsl:template>

<xsl:template mode="#all" match="xld:ul">
  <ul>
  <xsl:apply-templates/>
  </ul>
</xsl:template>

</xsl:stylesheet>

