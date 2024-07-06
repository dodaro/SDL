#!/bin/bash

binary=`poetry env info --path`
venv=`poetry env list | sed "s/ (Activated)//"`
poetry env use "$binary/../$venv/bin/python" 1>&2
poetry run python grammar.py -p </dev/stdin


