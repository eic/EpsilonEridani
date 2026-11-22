#!/usr/bin/env bash
# Toolchain-shaped Lake wrapper: put one hard deadline around each Lean process.
#
# Lean runs in its own process group. At the deadline the whole group gets TERM
# (then CONT), and KILL after the grace period, so descendants that ignore TERM
# cannot outlive the deadline. This is done here rather than with timeout(1)
# because its group-signalling behaviour is implementation-specific: the uutils
# timeout shipped as /usr/bin/timeout on ubuntu-26.04 runners does not deliver the
# --kill-after KILL to the process group, which left a TERM-ignoring grandchild
# running past the deadline. The production bwrap environment does not pass the
# TAUCETI_* variables below; they exist only so the trusted unit test can exercise
# this in milliseconds rather than minutes.
#
# The deadline bounds a single Lean process so a candidate cannot hang the job with a
# non-terminating elaboration or `initialize` block. It is a liveness bound, not a
# performance budget: the performance gate measures cost separately and has its own
# thresholds. So it only has to be low enough that a wedged process is caught in
# reasonable time, and comfortably above the slowest legitimate process.
#
# It was 300s, which the environment linter had quietly grown into: that one process was
# taking a median of 267s, so about one run in ten was being killed while making normal
# progress, and a change of a few seconds either way moved that rate a lot. A liveness
# bound sitting 11% above the slowest real workload is not doing the job it was added for.
#
# 3000s is deliberately far above anything legitimate rather than a little above it. Every
# second between the slowest real process and this bound is false-positive surface, and a
# wedged process is still caught well inside the job timeout, so there is nothing to buy by
# keeping it tight. Growth in the library should not require revisiting this number.
set -uo pipefail

deadline="${TAUCETI_LEAN_TIMEOUT_SECONDS:-3000}"
grace="${TAUCETI_LEAN_KILL_GRACE_SECONDS:-30}"
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
toolchain_root=${script_dir%/bin}

# Lake probes the command named by LEAN, then reconstructs <reported-prefix>/bin/lean.
# Reporting this wrapper's prepared, read-only toolchain root keeps every later
# compiler invocation on the wrapper instead of silently switching back to the
# underlying executable.
if [ "$#" = 1 ] && [ "$1" = --print-prefix ]; then
  printf '%s\n' "$toolchain_root"
  exit 0
fi

lean_command="$script_dir/lean-real"
if [ ! -x "$lean_command" ]; then
  echo "error: trusted Lean watchdog toolchain is missing bin/lean-real" >&2
  exit 127
fi

# Job control gives each background job its own process group, led by the job's
# first process, so `kill -- -PID` reaches every descendant of that process.
set -m
"$lean_command" "$@" &
child=$!
# The timer exits 0 once it has fired, and dies of TERM (status 143) if it is
# cancelled before the deadline. After firing it waits with the interruptible
# `wait` builtin so a cancellation during the grace period still reports 0.
(
  set +m  # keep the timer's own sleeps in its group, so cancelling it reaps them
  sleep "$deadline"
  kill -TERM -- "-$child" 2>/dev/null || exit 1
  kill -CONT -- "-$child" 2>/dev/null
  trap 'exit 0' TERM
  sleep "$grace" &
  wait "$!"
  kill -KILL -- "-$child" 2>/dev/null
  exit 0
) </dev/null >/dev/null 2>&1 &
timer=$!
set +m

wait "$child" 2>/dev/null  # silence the shell's own "Killed" job notice
status=$?
kill -TERM -- "-$timer" 2>/dev/null
wait "$timer"
if [ "$?" = 0 ]; then
  # The leader has exited; reap any descendant that outlived it.
  kill -KILL -- "-$child" 2>/dev/null
  [ "$status" = 137 ] || status=124
  source='<unknown module>'
  for argument in "$@"; do
    case "$argument" in *.lean) source="$argument" ;; esac
  done
  echo "error: Lean process for $source exceeded the ${deadline}s wall-clock limit (TERM, then KILL after ${grace}s)" >&2
fi
exit "$status"
