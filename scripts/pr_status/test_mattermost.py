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
