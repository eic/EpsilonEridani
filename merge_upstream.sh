#!/bin/bash
# A helper script to pull upstream infrastructure changes from TauCetiProject
# without causing merge conflicts with the actual math library contents.

git fetch upstream

# Start the merge, prioritizing our own file contents for any direct conflicts
git merge upstream/main -X ours --no-commit || true

# If upstream added new files to TauCeti/, they will reappear here. Delete them.
rm -rf TauCeti/ 2>/dev/null || true
git rm -rf TauCeti/ 2>/dev/null || true

# If upstream modified files that we deleted from EpsilonEridani/ (formerly TauCeti/),
# git will flag a modify/delete conflict and leave the upstream file.
# We ensure EpsilonEridani/ exactly matches our HEAD (keeping upstream math out).
git checkout HEAD -- EpsilonEridani/
git clean -fd EpsilonEridani/

# Finalize the merge
git commit -m "chore: merge upstream infrastructure, dropping upstream math content"
echo "Upstream merged successfully without math content conflicts!"
