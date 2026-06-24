#!/bin/bash

MODE=asp

if [ -n "$1" ]; then
  if [[ "$1" != "asp" && "$1" != "minizinc" ]]; then
    echo "Error: Argument must be 'asp' or 'minizinc'." >&2
    exit 1
  fi
  MODE="$1"
fi

binary=`poetry env info --path`
venv=`poetry env list | grep Activated | sed "s/ (Activated)//"`
poetry env use "$binary/../$venv/bin/python" 1>&2
if [ "$MODE" = "asp" ]; then
  poetry run python Validator.py --print-program /dev/stdin
else
  poetry run python Validator.py -t minizinc --file /dev/stdout /dev/stdin
fi

