#!/usr/bin/env python3
"""Drop the machine-dependent search time from committed trace files, so `make demo` leaves the tree clean."""
import json, sys
for p in sys.argv[1:]:
    d = json.load(open(p))
    d.pop("search_ms", None)
    open(p, "w").write(json.dumps(d))
