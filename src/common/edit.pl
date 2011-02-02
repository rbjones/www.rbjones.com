#! /usr/bin/perl -nw

if (/\\indexentry{!/) {
            s/"/\\"/g;
            while (/([^"])([@!|])/) {s/([^"])([@!|])/$1"$2/g};
	    s/indexentry{"!/indexentry{/;
            s/"\|hyperpage/\|hyperpage/};
print;
