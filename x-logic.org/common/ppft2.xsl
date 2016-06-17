<?xml version="1.0" encoding="iso-8859-1"?>

<!-- stylesheet for transforming ProofPower related formal materials into xhtml -->

<xsl:stylesheet
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0"
  xmlns="http://www.w3.org/1999/xhtml"
  xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
  exclude-result-prefixes="xld">

<xsl:template mode="index" match="xld:ft">
</xsl:template>

<xsl:template mode="mainframe" match="xld:ft[@lang='xl-ign']">
</xsl:template>

<xsl:template mode="mainframe" match="xld:ft[not(@lang='xl-ign')]">
<xsl:call-template name="break"/>
<xsl:call-template name="newline"/>
<table class="{@lang}" cellspacing="0" border="1" align="center">
<tr>
 <td class="{@lang}"><div class="xlft"><xsl:value-of select="@lang"/></div>
<xsl:call-template name="newline"/>
      <xsl:apply-templates mode="mainframe"/>
<xsl:call-template name="newline"/>
</td></tr></table>
<xsl:call-template name="break"/>
<xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:holconst">
<xsl:call-template name="break"/>
<xsl:call-template name="newline"/>
<table class="xl-holconst" cellspacing="0" border="1" align="center">
<xsl:call-template name="newline"/>
      <xsl:apply-templates mode="mainframe"/>
<xsl:call-template name="newline"/>
</table>
<xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:holpred">
<xsl:call-template name="newline"/>
<tr>
  <td class="xl-holconst">
    <xsl:apply-templates mode="mainframe"/>
  </td>
</tr>
<xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:holsig">
<tr>
  <td class="xl-holconst">
  <div class="xlft"><xsl:text>xl-holconst</xsl:text></div>
    <xsl:apply-templates mode="mainframe"/>
  </td>
</tr>
<xsl:call-template name="newline"/>
</xsl:template>

<xsl:template mode="mainframe" match="xld:ftbr">
  <xsl:text disable-output-escaping="yes"> &lt;br /&gt; </xsl:text>
  <xsl:if test="@indent">
    <img src="{concat($imagepath,'fill.gif')}" width="{@indent*7}" height="1" alt="ftbr"/>
  </xsl:if>
</xsl:template>

<xsl:template mode="mainframe" match="xld:fttab">
  <img src="{concat($imagepath,'fill.gif')}" width="30" height="1" alt="fttab"/>
</xsl:template>

<xsl:template name="break">
  <xsl:text disable-output-escaping="yes">&lt;br /&gt;</xsl:text>
</xsl:template>

<xsl:template mode="mainframe" match="xld:pptlt">
  <table class="pptl" align="center"><tr class="pptl" valign="top">
    <xsl:apply-templates mode="mainframe"/>
  </tr></table>
</xsl:template>

<xsl:template mode="mainframe" match="xld:pptlo">
  <table class="pptl" align="center">
    <xsl:apply-templates mode="mainframe"/>
  </table>
</xsl:template>

<xsl:template mode="mainframe" match="xld:entry">
  <tr class="pptl" valign="top">
    <td class="pptl">
      <xsl:apply-templates mode="mainframe" select="xld:name"/>
    </td>
      <xsl:apply-templates mode="mainframe" select="xld:value"/>
  </tr>
</xsl:template>

<xsl:template mode="mainframe" match="xld:col">
  <td class="pptl">
    <xsl:apply-templates mode="mainframe"/>
  </td>
</xsl:template>

<xsl:template mode="mainframe" match="xld:name">
    <div class="name">
      <xsl:apply-templates mode="mainframe"/>
    </div>
</xsl:template>

<xsl:template mode="mainframe" match="xld:value">
  <td class="pptl">
    <xsl:apply-templates mode="mainframe"/>
  </td>
</xsl:template>

</xsl:stylesheet>

