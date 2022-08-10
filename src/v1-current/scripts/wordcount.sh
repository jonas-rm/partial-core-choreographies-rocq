#!/bin/sh

for word in Definition Theorem Lemma Fixpoint Inductive Record; do
	echo "# $word"
	for f in *.v; do
		echo -n "	$f: "
		grep -o "$word\b" $f | wc -l
	done
done