#!/usr/bin/env bash
# aristotle-integrate.sh — extract an Aristotle result tarball, diff, and
# show next steps for integration.
#
# Usage: scripts/aristotle-integrate.sh <project-id-prefix>
#
# Looks for /tmp/aristotle-*-${TS}.tar.gz files matching the project,
# extracts to /tmp/aristotle-out-${PREFIX}/, and prints the diff.

set -euo pipefail

if [ $# -lt 1 ]; then
  echo "Usage: $0 <project-id-prefix>" >&2
  echo "Example: $0 4cda6cb1" >&2
  exit 1
fi

PREFIX="$1"

# Find the tarball matching the prefix or most recent if exact filename absent.
TARBALL=$(ls -t /tmp/aristotle-*.tar.gz 2>/dev/null | head -1)

if [ -z "${TARBALL:-}" ]; then
  echo "No Aristotle result tarballs found in /tmp/" >&2
  exit 1
fi

echo "Tarball: $TARBALL"

# Extract to sandbox
SANDBOX="/tmp/aristotle-out-$PREFIX"
rm -rf "$SANDBOX"
mkdir -p "$SANDBOX"
tar -xzf "$TARBALL" -C "$SANDBOX"

# Aristotle wraps everything in `project_aristotle/`
PROJECT_DIR="$SANDBOX/project_aristotle"
if [ ! -d "$PROJECT_DIR" ]; then
  PROJECT_DIR="$SANDBOX"
fi

echo ""
echo "=== Aristotle summary ==="
if [ -f "$PROJECT_DIR/ARISTOTLE_SUMMARY.md" ]; then
  cat "$PROJECT_DIR/ARISTOTLE_SUMMARY.md"
else
  echo "(no ARISTOTLE_SUMMARY.md)"
fi

echo ""
echo "=== Files that differ ==="
diff -rq BlockSynchroniser "$PROJECT_DIR/BlockSynchroniser" 2>&1 | head -30 || true

echo ""
echo "=== Next steps ==="
echo "1. Inspect diffs:  diff -u BlockSynchroniser/<file>.lean $PROJECT_DIR/BlockSynchroniser/<file>.lean"
echo "2. Apply (per-file): cp $PROJECT_DIR/BlockSynchroniser/<file>.lean BlockSynchroniser/<file>.lean"
echo "3. Add provenance:  '-- proof: aristotle (project $PREFIX)' above each filled theorem"
echo "4. Verify:  lake build"
echo "5. Update docs/aristotle-projects.md (move to Completed)"
echo "6. Update docs/aristotle-attributions.md (new project section)"
echo "7. Commit:  git commit -m 'integrate aristotle round XX (project $PREFIX...)'"
