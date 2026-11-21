"""A fake `gh` for tests of scripts that shell out to `gh api`.

`install(directory, responses)` writes an executable `gh` into `directory/bin` and the canned
responses next to it, and returns the environment to run the script under: PATH with the fake first,
and FAKE_GH_DB / FAKE_GH_LOG. `responses` maps an API path to the JSON it answers; a path with a
query string matches exactly first, then without the query. `--jq` is applied by the real `jq`. A
path with no response answers 404 on stderr and exits 1, like `gh`. Each requested path is appended to
the log, which `calls(directory)` reads back.

Used by test_check_bump.py and test_lint_scope.py, both of which skip without `jq` on PATH.
"""

import json
import os
import stat
import textwrap
from pathlib import Path

FAKE_GH = textwrap.dedent('''\
    #!/usr/bin/env python3
    import json, os, subprocess, sys
    args = sys.argv[1:]
    assert args[0] == "api", args
    jq = args[args.index("--jq") + 1] if "--jq" in args else None
    path = next(a for a in args[1:] if not a.startswith("-") and a != jq)
    responses = json.load(open(os.environ["FAKE_GH_DB"]))
    with open(os.environ["FAKE_GH_LOG"], "a") as log:
        log.write(path + "\\n")
    key = path if path in responses else path.split("?")[0]
    if key not in responses:
        sys.stderr.write(f"gh: Not Found (HTTP 404) {path}\\n")
        sys.exit(1)
    body = json.dumps(responses[key])
    if jq is None:
        print(body)
        sys.exit(0)
    out = subprocess.run(["jq", "-r", jq], input=body, capture_output=True, text=True)
    sys.stdout.write(out.stdout)
    sys.exit(out.returncode)
''')


def install(directory, responses):
    """Put the fake `gh` and `responses` under `directory`; the environment to run a script with."""
    directory = Path(directory)
    gh = directory / "bin" / "gh"
    gh.parent.mkdir(exist_ok=True)
    gh.write_text(FAKE_GH)
    gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
    (directory / "db.json").write_text(json.dumps(responses))
    return dict(os.environ, PATH=f"{gh.parent}:{os.environ['PATH']}",
                FAKE_GH_DB=str(directory / "db.json"), FAKE_GH_LOG=str(directory / "gh.log"))


def calls(directory):
    """The API paths requested so far, in order."""
    log = Path(directory) / "gh.log"
    return log.read_text().splitlines() if log.exists() else []
