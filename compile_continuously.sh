#!/bin/bash
set -e

./compile.sh || true
fswatcher --throttle 300 --path src/Main.agda ./compile.sh
