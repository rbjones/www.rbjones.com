// convert all characters to lowercase to simplify testing
var agt=navigator.userAgent.toLowerCase();
// *** BROWSER VERSION ***
    var is_major = parseInt(navigator.appVersion);
    var is_minor = parseFloat(navigator.appVersion);

    var is_nav  = ((agt.indexOf('mozilla')!=-1) && (agt.indexOf('spoofer')==-1)
                && (agt.indexOf('compatible') == -1) && (agt.indexOf('opera')==-1)
                && (agt.indexOf('webtv')==-1));

    var is_ie   = (agt.indexOf("msie") != -1);
    // *** PLATFORM ***
    var is_win   = ( (agt.indexOf("win")!=-1) || (agt.indexOf("16bit")!=-1) );

if (is_win && is_nav) 
  {
  document.write('<LINK REL=STYLESHEET TYPE="text/css" HREF="'+root+'prof/p2sty.txt" TITLE="Factasia style for Navigator on windows.">')
  }
  else if (is_nav)
  {
  document.write('<LINK REL=STYLESHEET TYPE="text/css" HREF="'+root+'prof/p2sty.txt" TITLE="Factasia style for Navigator not on windows.">')
  }
  else
  {
  document.write('<LINK REL=STYLESHEET TYPE="text/css" HREF="'+root+'prof/p1sty.txt" TITLE="Factasia style for ie">')
  }
