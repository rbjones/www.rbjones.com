#!/usr/bin/perl -w
# ($Id)

$input="mkaris_metaphysics.txt";
$output="mkaris_metaphysics2.txt";
print "input: $input output: $output\n";
$_=<STDIN>;
open (INPUT,$input);
open (OUTPUT,"> $output");
while ($_=<INPUT>) {s/\r//g; print OUTPUT};
