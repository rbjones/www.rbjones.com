#!/usr/bin/perl -w
# ($Id)

while ($_=<STDIN>) {
     s/\r/<CR>/;
     s/\n/<NL>/;
     s/\l/<LF>\l/;
    print};
