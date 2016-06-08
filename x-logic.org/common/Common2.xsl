<?xml version="1.0" encoding="utf-8"?>

<!-- stylesheet for transforming xml xldoc into xhtml -->
<!-- material common to frame, index and mainframe -->

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="2.0"
				xmlns="http://www.w3.org/1999/xhtml"
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

<xsl:template mode="#all" match="xld:hide"/>

<xsl:template mode="#all" match="xld:rbjgif">
 <img src="{concat($rootpath,'rbjgif/',@name)}">
    <xsl:for-each select="@*">
      <xsl:copy/>
    </xsl:for-each>
 </img>
</xsl:template>

<xsl:template name="XHTML1Strict">
  <xsl:text disable-output-escaping="yes">
    &#xA;&lt;!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
               "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd"&gt;</xsl:text>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template name="XHTML1Transitional">
  <xsl:text disable-output-escaping="yes">
    &#xA;&lt;!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN"
     "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd"&gt;
  </xsl:text>
  <xsl:call-template name="newline"/>
</xsl:template>

<xsl:template name="newline">
  <xsl:text>&#xA;</xsl:text>
</xsl:template>

<xsl:template name="copyright">
  <xsl:text disable-output-escaping="yes">&amp;copy;</xsl:text>
</xsl:template>

<xsl:template name="valid_xhtml10">
      <a href="http://validator.w3.org/check/referer">V</a>
</xsl:template>

<xsl:template name="valid_xhtml10_b">
  <p>
      <a href="http://validator.w3.org/check/referer">
        <img src="http://www.w3.org/Icons/valid-xhtml10"
          alt="Valid XHTML 1.0!" height="31" width="88" border="0"/>
      </a>
  </p>
</xsl:template>

</xsl:stylesheet>

