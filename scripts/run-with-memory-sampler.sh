#!/usr/bin/env bash
# run-with-memory-sampler.sh — run a command while sampling memory, for the doc-gen4 steps of
# .github/workflows/pages.yml.
#
# Usage: bash scripts/run-with-memory-sampler.sh <label> <command> [args...]
#
# Diagnostics for the ENOMEM failures on ubuntu-26.04 (`resource exhausted (error code: 12,
# not enough memory)` when Lake forks git and lean). Lean starts child processes with fork(),
# so the samples record Lake's own size and largest mappings alongside system memory, to tell a
# single oversized mapping apart from genuine exhaustion. The sampler only writes to a log file
# that is printed afterwards; the command and its exit status are unchanged.
set -uo pipefail

label="$1"
shift

diag="${RUNNER_TEMP:-/tmp}/docgen-memory-${label}.log"
cg="/sys/fs/cgroup$(sed -n 's/^0:://p' /proc/self/cgroup)"
{
  echo "kernel $(uname -r), nproc $(nproc)"
  echo "cgroup $cg memory.max=$(cat "$cg/memory.max" 2>/dev/null || echo n/a)"
} > "$diag"
(
  set +e
  while :; do
    {
      echo "=== $(date -u +%H:%M:%S)"
      grep -E '^(MemAvailable|SwapFree|Committed_AS|CommitLimit):' /proc/meminfo \
        | tr -s ' ' | paste -sd ' '
      ps -eo pid,rss,vsz,etimes,args --sort=-rss | head -6 | cut -c1-160
      for pid in $(pgrep -x lake); do
        grep -E '^Vm(Peak|Size|HWM|RSS):' "/proc/$pid/status" \
          | tr -s ' \t' ' ' | paste -sd ' ' | sed "s/^/lake $pid: /"
        pmap -x "$pid" | sort -n -k2 | tail -3
      done
    } >> "$diag" 2>&1
    sleep 10
  done
) &
sampler=$!

status=0
"$@" || status=$?
kill "$sampler" 2>/dev/null || true

echo "::group::doc-gen4 memory samples ($label)"
cat "$diag"
echo "::endgroup::"
echo "cgroup memory.peak=$(cat "$cg/memory.peak" 2>/dev/null || echo n/a)"
echo "cgroup memory.events: $(paste -sd ' ' "$cg/memory.events" 2>/dev/null || echo n/a)"
if [ "$status" != 0 ]; then
  echo "::group::kernel log (tail)"
  sudo -n dmesg -T 2>&1 | tail -60 || true
  echo "::endgroup::"
fi
exit "$status"
