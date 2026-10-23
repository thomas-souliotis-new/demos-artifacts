#!/bin/sh
# Machine-check every EasyCrypt file of the artifact and fail on any admit.
set -eu
cd "$(dirname "$0")"
if grep -n 'admit' *.ec *.eca 2>/dev/null; then
  echo "error: admit found" >&2
  exit 1
fi
for f in $(cat FILES); do
  echo "== $f"
  easycrypt compile -no-eco "$f"
done
echo "All files checked."
