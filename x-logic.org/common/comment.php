<?php

# $Id: comment.php,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $

include("mainfile.php");

dbconnect();

$result = mysql_query("select sid, title, hometext, bodytext, comments, topic, informant, notes, url ".
  "FROM webpages where url=\"$docurl\"");

list($sid, $title, $hometext, $bodytext, $comments, $topic, $informant, $notes, $url)
  = mysql_fetch_row($result);

if ($comments > 0) {
  $comtext=sprintf("%d",$comments);
  echo "<tr valign=\"top\" align=\"center\"><td class=\"i\">\n";
  echo "<a class=\"i\" target=\"_top\" href=\"$root";
  echo "phpnuke/webarticle.php?op=viewComments&pid=0&sid=$sid\">view ";
  if ($comments > 1) {
    echo "$comtext comments";
  } else {
    echo "comment";
  }
  echo "</a>\n</td></tr>\n";
  echo "<tr valign=\"top\" align=\"center\"><td class=\"i\">\n";
  echo "<a class=\"i\" target=\"_top\" href=\"$root"."phpnuke/webcomments.php?op=Reply&pid=0&sid=$sid\">add comment</a>\n";
  echo "</td></tr>\n";
}
else {
  $doctitle=ereg_replace(" ","%20",$doctitle);
  $commandpath=$root."phpnuke/webcomments.php";
  echo "<tr valign=\"top\" align=\"center\"><td class=\"i\">\n";
  echo "<a class=\"i\" target=\"_top\" href=\"$root"."phpnuke/webcomments.php?op=submitFirstComment&title=$doctitle&url=$docurl&site=$domain\">add comment</a>\n";
  echo "</td></tr>\n";
}
?>
