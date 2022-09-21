#!/bin/bash
set -e

clear
agda \
  --library standard-library \
  --include-path src \
  --include-path examples \
  examples/Main.agda
