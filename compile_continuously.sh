#!/bin/bash
set -e

if [ ! -f "$1" ]; then
  echo "usage: $0 src/Category.agda"
  echo
  echo "A poor man's IDE. Recompiles the given file when it changes."
  exit 1
fi

./compile.sh "$1" || true
fswatcher --throttle 300 --path "$1" -- ./compile.sh "$1"
