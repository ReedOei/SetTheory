#!/usr/bin/env bash

grammar_file="$1"
output_file="$2"

if [[ -z "$grammar_file" ]]; then
    grammar_file="grammar.lark"
fi

if [[ -z "$output_file" ]]; then
    output_file="lark_parser.py"
fi

python3 -m lark.tools.standalone "$grammar_file" "start" > "$output_file"

echo "Grammar size (lines, words, characters): "
python3 -m lark.tools.standalone "$grammar_file" "start" | wc

