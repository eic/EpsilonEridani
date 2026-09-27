#!/usr/bin/env python3
"""Mirror an EpsilonEridani PR's lifecycle onto Mattermost emoji reactions.

This script manages PR announcements and status tracking using the Mattermost API v4.
Unlike Zulip which uses Topics, Mattermost uses threaded replies. We uniquely identify
our announcement posts using a hidden markdown tag: [PR-###-ANNOUNCEMENT].

Usage:
    mattermost.py reconcile <pr_number> [--create|--create-if-open] [--strict] [--ci STATE]
    mattermost.py backfill [--dry-run] [--strict]  # JSONL PR states on stdin
    mattermost.py check
"""

import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request
import core

# We use the secrets injected by GitHub Actions.
BOT_TOKEN = os.environ.get("MATTERMOST_BOT_TOKEN", "").strip()
CHANNEL_ID = os.environ.get("MATTERMOST_CHANNEL_ID", "").strip()
URL = os.environ.get("MATTERMOST_URL", "").strip().rstrip("/")

class ConfigError(RuntimeError):
    pass

def api_request(method, path, data=None):
    if not URL or not BOT_TOKEN:
        raise ConfigError("MATTERMOST_URL or MATTERMOST_BOT_TOKEN not set.")
    
    url = f"{URL}/api/v4{path}"
    headers = {
        "Authorization": f"Bearer {BOT_TOKEN}",
        "Content-Type": "application/json",
        "Accept": "application/json"
    }
    
    body = None
    if data is not None:
        body = json.dumps(data).encode("utf-8")
        
    req = urllib.request.Request(url, data=body, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req) as response:
            body = response.read()
            return json.loads(body.decode("utf-8")) if body else None
    except urllib.error.HTTPError as e:
        if e.code in (401, 403):
            raise ConfigError(f"Mattermost auth failed ({e.code}): {e.read().decode('utf-8')}")
        raise RuntimeError(f"Mattermost API error ({e.code}): {e.read().decode('utf-8')}")

def check():
    print("Checking Mattermost credentials...")
    res = api_request("GET", "/users/me")
    print(f"OK: authenticated as bot user {res.get('username')} ({res.get('id')})")
    
    # Check channel access
    if CHANNEL_ID:
        try:
            api_request("GET", f"/channels/{CHANNEL_ID}")
            print(f"OK: have access to channel {CHANNEL_ID}")
        except Exception as e:
            raise ConfigError(f"Cannot access channel {CHANNEL_ID}: {e}")

def reconcile(pr, create=False, ci_override=None, create_if_open=False, state=None, dry_run=False):
    st = core.pr_state(pr) if state is None else state
    print(f"Reconciling PR #{pr}...")
    # NOTE: Full reconcile logic (search for hidden tag, edit post, update emojis) goes here.
    # This is a stub for the PR implementation.
    return 1

def backfill(rows, dry_run=False):
    print("Backfilling...")
    seen = changes = 0
    failures = []
    return seen, changes, failures

def fail_config(msg):
    print(f"CONFIG ERROR: {msg}", file=sys.stderr)
    if os.environ.get("GITHUB_ACTIONS") == "true":
        safe = msg.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
        print(f"::error title=Mattermost integration is broken::{safe}", flush=True)
    return 1

def main(argv):
    cmd = argv[1] if len(argv) > 1 else None
    if not (BOT_TOKEN and URL) and cmd != "check":
        # In actual usage without a token, workflows will skip via bash check, 
        # but just in case, handle it gracefully.
        print("No MATTERMOST_BOT_TOKEN or URL set, skipping.")
        return 0
        
    if cmd == "check":
        try:
            check()
            return 0
        except ConfigError as e:
            return fail_config(str(e))
            
    if cmd == "reconcile":
        if len(argv) <= 2:
            print("Missing PR number")
            return 2
        pr = argv[2].lstrip("#")
        if not pr.isdigit():
            print(f"Not a PR number: {pr}")
            return 0
        rest = argv[3:]
        create = "--create" in rest
        create_if_open = "--create-if-open" in rest
        strict = "--strict" in rest
        ci_override = None
        if "--ci" in rest:
            ci_override = rest[rest.index("--ci") + 1]
            
        try:
            reconcile(pr, create=create, create_if_open=create_if_open, ci_override=ci_override)
            return 0
        except ConfigError as e:
            return fail_config(str(e))
            
    if cmd == "backfill":
        rest = argv[2:]
        dry_run = "--dry-run" in rest
        try:
            backfill(sys.stdin, dry_run=dry_run)
            return 0
        except ConfigError as e:
            return fail_config(str(e))
            
    print(__doc__)
    return 2

if __name__ == "__main__":
    sys.exit(main(sys.argv))
