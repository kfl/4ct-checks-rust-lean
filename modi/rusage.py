#!/usr/bin/env python3
"""Run a command and write "wall=..s user=..s sys=..s maxrss=..kB" to a
file: a portable stand-in for GNU `time -v`, which the MODI stock image
lacks. Usage: rusage.py <outfile> <cmd> [args...]"""
import resource, subprocess, sys, time

out, cmd = sys.argv[1], sys.argv[2:]
t0 = time.monotonic()
rc = subprocess.run(cmd).returncode
wall = time.monotonic() - t0
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
maxrss_kb = ru.ru_maxrss // 1024 if sys.platform == "darwin" else ru.ru_maxrss
with open(out, "w") as f:
    f.write(f"wall={wall:.2f}s user={ru.ru_utime:.2f}s "
            f"sys={ru.ru_stime:.2f}s maxrss={maxrss_kb}kB\n")
sys.exit(rc)
