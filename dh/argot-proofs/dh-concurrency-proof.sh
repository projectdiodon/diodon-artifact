#!/bin/bash

# exit when any command fails
set -e

# Script to run the goroutine analysis proof on the DH implementation

PWD=$(dirname "$0")
SCRIPT_DIR=$(realpath "$PWD")
AGENT_DIR="$SCRIPT_DIR"/../implementation
ARGOT_BIN=argot

if [ ! -e "$AGENT_DIR" ]; then
    echo Error: "$AGENT_DIR" does not exist
    exit 1
fi
cd "$AGENT_DIR" || exit

echo "Running goroutine analysis on DH implementation in directory $(pwd)"

"$ARGOT_BIN" goroutine -config "$SCRIPT_DIR"/argot-config-dh.yaml