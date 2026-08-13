#!/bin/sh

SCRIPT_DIR=$(cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd)
SOURCE_DIR="$SCRIPT_DIR/../src"

for word in Definition Fixpoint Record Inductive Lemma Theorem Example Ltac; do
	echo "# $word"
	for f in "$SOURCE_DIR"/*.v; do
    echo -n "	$(basename $f): "
		grep -o "$word\b" $f | wc -l
	done
done
