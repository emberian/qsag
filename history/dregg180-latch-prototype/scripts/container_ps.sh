#!/bin/sh
# List the processes inside this lane's own build container (PID, age in s, command line).
# With "stop <pid>...", stop exactly those PIDs after re-reading their command lines.
if [ "$1" = stop ]; then
    shift
    for p in "$@"; do
        c=$(tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null | cut -c1-60)
        echo "stopping $p: $c"
        kill "$p" 2>/dev/null || true
    done
    exit 0
fi
now=$(cut -d' ' -f1 /proc/uptime | cut -d. -f1)
for d in /proc/[0-9]*; do
    p=${d#/proc/}
    c=$(tr '\0' ' ' < $d/cmdline 2>/dev/null | cut -c1-90)
    [ -z "$c" ] && continue
    st=$(awk '{print int($22/100)}' $d/stat 2>/dev/null)
    echo "$p $((now - st))s $c"
done
