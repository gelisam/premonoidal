#!/bin/bash
set -e

clear
agda \
  --library standard-library \
  --include-path src \
  src/Main.agda
