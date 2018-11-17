#!/bin/bash
set -e

if [ ! -f "$1" ]; then
  echo "usage: $0 src/Category.agda"
  echo
  echo "A poor man's IDE. Recompiles the given file when it changes."
  exit 1
fi

clear
agda \
  --library standard-library \
  --include-path src \
  "$@"
