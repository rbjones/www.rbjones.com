<?xml version="1.0" encoding="iso-8859-1"?>

<!-- stylesheet of X-Logic site specifics and defaults -->

<xsl:stylesheet
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="2.0"
  xmlns="http://www.w3.org/1999/xhtml"
  xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
  xsl:exclude-result-prefixes="xld">

<xsl:template name="author">
  <xsl:if test="ancestor-or-self::xld:xldoc/@author='rbj'">
    <xsl:text disable-output-escaping="yes"> &amp;copy; </xsl:text>
    <a target="_top" href="http://www.rbjones.com/rbjpub/rbj.htm"><img src="{$imagepath}rbjin1.gif" alt="RBJ" border="0" align="bottom"/></a>
  </xsl:if>
  <xsl:if test="ancestor-or-self::xld:xldoc/@rbjhome">
    <xsl:text disable-output-escaping="yes"> &amp;copy; </xsl:text>
    <a target="_top" href="http://www.rbjones.com/rbjpub/rbj.htm"><img src="{$imagepath}rbjin1.gif" alt="RBJ" border="0" align="bottom"/></a>
  </xsl:if>
</xsl:template>

<xsl:template name="privacy">
    <a target="_top" href="{concat($rootpath,'rbjpub/privacy.html')}">privacy policy</a>
</xsl:template>

<xsl:template name="site">
  <xsl:param name="site">
      <xsl:if test="@site"><xsl:value-of select="@site"/></xsl:if>
  </xsl:param>
  <xsl:if test="$site='rbjones'">
    <xsl:text>//http:/www.rbjones.com/</xsl:text>
  </xsl:if>
  <xsl:if test="$site='x-logic'">
    <xsl:text>//http:/www.x-logic.org/</xsl:text>
  </xsl:if>
  <xsl:if test="$site='openbrand'">
    <xsl:text>//http:/www.openbrand.org/</xsl:text>
  </xsl:if>
</xsl:template>

<xsl:template name="sitesrc">
  <xsl:param name="site">
      <xsl:if test="@site"><xsl:value-of select="@site"/></xsl:if>
  </xsl:param>
  <xsl:if test="$site='rbjones'">
    <xsl:text>/home/rbj/rbjones/work/</xsl:text>
  </xsl:if>
  <xsl:if test="$site='x-logic'">
    <xsl:text>/home/x-logic/x-logic/work/</xsl:text>
  </xsl:if>
  <xsl:if test="$site='openbrand'">
    <xsl:text>/home/openbran/OpenBrand/work/</xsl:text>
  </xsl:if>
</xsl:template>

</xsl:stylesheet>



