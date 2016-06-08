#!/bin/bash
make $1.doc
if test $2 
then xpp -file $1.doc -command pp -d $2 
else  xpp -file $1.doc 
fi
make $1.xdoc

