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

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
				version="1.0"
				xmlns="http://www.w3.org/TR/xhtml1/strict"
				xmlns:xld="http://www.x-logic.org/xmlns/draft/xld"
				exclude-result-prefixes="xld">

<xsl:template match="xld:p">
  <p>
  <xsl:apply-templates/>
  </p>
</xsl:template>

<xsl:template match="xld:br">
  <br/>
</xsl:template>

</xsl:stylesheet>

