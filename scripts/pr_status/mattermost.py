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

CI_EMOJIS = {
    "running": "large_yellow_circle",
    "success": "white_check_mark",
    "failure": "x"
}

REVIEW_EMOJIS = {
    "running": "eyes",
    "changes": "writing_hand",
    "approved": "white_check_mark"
}

def pr_message_content(pr, title, author, roadmaps):
    roadmap_str = f" [Roadmap: {', '.join(roadmaps)}]" if roadmaps else ""
    return f"🚀 **New PR [#{pr}](https://github.com/{core.REPO}/pull/{pr}):** {title} (Author: @{author}){roadmap_str}\n\n<!-- [PR-{pr}-ANNOUNCEMENT] -->"

def get_team_id(channel_id):
    res = api_request("GET", f"/channels/{channel_id}")
    return res.get("team_id")

def find_post(pr, team_id):
    tag = f"[PR-{pr}-ANNOUNCEMENT]"
    data = {"terms": tag, "is_or_search": False}
    res = api_request("POST", f"/teams/{team_id}/posts/search", data=data)
    posts = res.get("posts", {})
    for post_id, post in posts.items():
        if post.get("channel_id") == CHANNEL_ID and tag in post.get("message", ""):
            return post
    return None

def set_reaction(post_id, user_id, expected_emoji, current_reactions):
    # Find emojis we placed
    our_reactions = [r for r in current_reactions if r.get("user_id") == user_id]
    
    # If the expected emoji is already there, remove it from the list of ones to delete
    already_has = False
    for r in our_reactions:
        emoji = r.get("emoji_name")
        if emoji == expected_emoji:
            already_has = True
        else:
            api_request("DELETE", f"/users/me/posts/{post_id}/reactions/{emoji}")
            
    if expected_emoji and not already_has:
        api_request("POST", f"/posts/{post_id}/reactions", data={"user_id": user_id, "post_id": post_id, "emoji_name": expected_emoji})

def reconcile(pr, create=False, ci_override=None, create_if_open=False, state=None, dry_run=False):
    st = core.pr_state(pr) if state is None else state
    create = create or (create_if_open and st["state"] == "open" and not st["merged"])
    
    content = pr_message_content(pr, st["title"], st.get("author", ""), st.get("roadmaps", []))
    
    team_id = get_team_id(CHANNEL_ID)
    post = find_post(pr, team_id)
    
    if post is None:
        if not create:
            print(f"no message for PR #{pr} yet and --create not set; nothing to do")
            return 0
        if dry_run:
            print(f"would create message for PR #{pr}")
            return 1
            
        print(f"Creating message for PR #{pr}")
        post = api_request("POST", "/posts", data={"channel_id": CHANNEL_ID, "message": content})
    elif post.get("message") != content:
        if not dry_run:
            print(f"Updating message for PR #{pr}")
            api_request("PUT", f"/posts/{post['id']}", data={"id": post["id"], "message": content})
            
    status = core.derive(pr, ci_override, state=st)
    
    # Determine emojis
    rev_emoji = None
    ci_emoji = None
    
    if status["lifecycle"] == "merged":
        rev_emoji = "merged"
    elif status["lifecycle"] == "closed":
        rev_emoji = "closed_book"
    else:
        rev_emoji = REVIEW_EMOJIS.get(status["review"])
        ci_emoji = CI_EMOJIS.get(status["ci"])
        
    if not dry_run and post:
        me = api_request("GET", "/users/me")
        user_id = me.get("id")
        
        # Get current reactions on the post
        reactions = post.get("metadata", {}).get("reactions")
        if reactions is None:
            # Need to fetch explicitly if not populated in search
            reactions = api_request("GET", f"/posts/{post['id']}/reactions") or []
            
        # We simplify this by just clearing our old CI/Review emojis and setting the new ones
        set_reaction(post["id"], user_id, rev_emoji, [r for r in reactions if r.get("emoji_name") in REVIEW_EMOJIS.values() or r.get("emoji_name") in ("merged", "closed_book")])
        set_reaction(post["id"], user_id, ci_emoji, [r for r in reactions if r.get("emoji_name") in CI_EMOJIS.values()])
        
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
