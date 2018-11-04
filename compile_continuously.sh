#!/bin/bash
set -e

./compile.sh "$@" || true
fswatcher --throttle 300 --path "$@" -- ./compile.sh "$@"
