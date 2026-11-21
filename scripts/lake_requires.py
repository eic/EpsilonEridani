"""The `require`s of a lakefile.toml, in declaration order.

The order matters: Lake takes the pins of the LAST require that pins a package, so the bump guard
(scripts/check-bump.sh, step 1b) and the resolver (scripts/resolve_deps.py) both read it from here
rather than each parsing the file. Needs python3.11+ for `tomllib`.
"""

import re
import tomllib


def repo_slug(url):
    """`owner/repo` of a GitHub repository URL, with or without scheme host, `.git` or trailing `/`:
    the one normalisation the guard and the resolver compare and query repositories by."""
    path = re.sub(r"^https?://github\.com/", "", (url or "").strip()).rstrip("/")
    return path.removesuffix(".git").rstrip("/")


def parse(text):
    """The lakefile's `[[require]]` tables, in order (each a dict with at least a `name`)."""
    return tomllib.loads(text).get("require", [])


def names(text):
    """The requires' names, in declaration order."""
    return [require["name"] for require in parse(text)]
