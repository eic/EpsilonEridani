import json
import pytest
from unittest.mock import patch, MagicMock

import mattermost

def test_backfill_collects_stats_and_failures():
    # Provide 3 lines:
    # 1. Valid JSON, successfully reconciles
    # 2. Invalid JSON (should fail)
    # 3. Valid JSON, but reconcile throws an exception (should fail)
    rows = [
        '{"number": 123, "state": "open", "merged": false}',
        '{"number": 124, "state"',
        '{"number": 125, "state": "open", "merged": false}',
    ]
    
    with patch("mattermost.reconcile") as mock_reconcile:
        # Mock reconcile to return 1 change for 123, and raise Exception for 125
        def side_effect(pr, **kwargs):
            if pr == "123":
                return 1
            elif pr == "125":
                raise Exception("Network error")
            return 0
        mock_reconcile.side_effect = side_effect
        
        seen, changes, failures = mattermost.backfill(rows, dry_run=True)
        
        # 2 lines were seen (parsed as JSON successfully)
        assert seen == 2
        # 1 change was returned by reconcile (for PR 123)
        assert changes == 1
        # 2 failures (1 for invalid JSON, 1 for exception in reconcile)
        assert len(failures) == 2
        assert failures[0] == '{"number": 124, "state"'
        assert failures[1] == '{"number": 125, "state": "open", "merged": false}'

@patch("mattermost.api_request")
@patch("mattermost.core.derive")
@patch("mattermost.find_post")
@patch("mattermost.get_team_id")
def test_reconcile_emojis(mock_team_id, mock_find_post, mock_derive, mock_api):
    mock_team_id.return_value = "team123"
    mock_find_post.return_value = {
        "id": "post123",
        "message": "🚀 **New PR [#123](https://github.com/eic/EpsilonEridani/pull/123):** test",
        "props": {"eic_pr": "123"}
    }
    
    def api_side_effect(method, url, data=None):
        if url == "/users/me":
            return {"id": "bot_user_id"}
        if url.endswith("/reactions") and method == "GET":
            return []
        return None
    mock_api.side_effect = api_side_effect
    
    mock_derive.return_value = {
        "lifecycle": "open",
        "ci": "success",
        "review": "white_check_mark"
    }
    
    mattermost.reconcile("123", state={"title": "test", "state": "closed", "merged": True, "author": "", "roadmaps": []})
    
    # Check that POST to /reactions was called with the right emojis
    mock_api.assert_any_call("POST", "/reactions", data={"user_id": "bot_user_id", "post_id": "post123", "emoji_name": "white_check_mark"})
    mock_api.assert_any_call("POST", "/reactions", data={"user_id": "bot_user_id", "post_id": "post123", "emoji_name": "white_check_mark"})
