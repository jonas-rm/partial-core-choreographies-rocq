#!/bin/sh

for word in Definition Fixpoint Record Inductive Lemma Example Ltac; do
	echo "# $word"
	for f in *.v; do
		echo -n "	$f: "
		grep -o "$word\b" $f | wc -l
	done
done