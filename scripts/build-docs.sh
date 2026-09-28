#!/bin/sh
# Refresh docs/: the tamper sweep (compiled tool), the widget's JavaScript, and the props Lean computes.
set -e
cd "$(dirname "$0")/.."
lake build
.lake/build/bin/x509 sweep > docs/sweep.json
lake build X509.Widget
cp widget/X509.js docs/X509.js
lake env lean --run scripts/Props.lean
