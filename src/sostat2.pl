# Variant of sostat.pl for digitalspace stats
#$created="2000-04-12";
#$modified="2016-06-28";

use stats;

$webdir=$ARGV[0];
$statsdir=$ARGV[1];
$inc=$ARGV[2];
$pinc=$inc-1;
$sfile=$ARGV[3];

print "sostat2: \$inc=$inc; \$sfile=$sfile\n \$webdir=$webdir";

$rbjpubdir="$webdir/rbjpub";
$top100="$rbjpubdir/rbj036.htm";
$ptop100="$rbjpubdir/rbj035.htm";
$ot100="$statsdir/t100$pinc.txt";
$nt100="$statsdir/t100$inc.txt";

$statsda="$statsdir/stdif_a$inc.txt";
$statsdn="$statsdir/stdif_n$inc.txt";
$statsdh="$statsdir/stdh$inc.txt";
$statsah="$statsdir/stah$inc.txt";

#print "statsda: $statsda; Statsdn: $statsdn; Statsdh: $statsdh; Statsah: $statsah\n";

%pages3=stats::load4("$statsdir/$sfile");

#print "output alphabetic, ";
$totalhitcount=stats::outal($statsda,%pages3);

#print "output numeric.\n";
$pagecount=stats::outnu($statsdn, %pages3);

#print "count directory hits\n";
%dpages=stats::dirhits(\%pages3);
$count=stats::outnu($statsdh,%dpages);

#print "agregate directory hits\n";
$dpages{"/pipermail/hist-analytic_rbjones.com"}=+0;
$dpages{"/pipermail/jlsblogs_rbjones.com"}=+0;
$dpages{"/pipermail/rbjblogs_rbjones.com"}=+0;
%adpages=stats::agdirhits(\%dpages);
$count=stats::outnu($statsah,%adpages);

#print "output top100.\n";
stats::outtop100($totalhitcount, $pagecount, $top100, $ptop100, $ot100, $nt100, %pages3);

#print "stats completed.\n";
