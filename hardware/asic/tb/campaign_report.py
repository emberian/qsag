"""Check the RTL result for each manifest bit and summarize rejection by proof field."""
from collections import Counter
from pathlib import Path
import re
import sys


def report(manifest, transcript, envelope_only):
    fields = {}
    for line in manifest.read_text().splitlines():
        offset, bit, field = line.split()
        key = int(offset), int(bit)
        if key in fields:
            raise ValueError(f"duplicate mutation {key}")
        fields[key] = field

    rejected = set()
    accepted = 0
    log = transcript.read_text()
    for offset, bit, status in re.findall(
        r"^AUTO proof=.*? flip=(-?\d+) bit=(\d+) .*? status=([\da-fA-F]+) ", log, re.M
    ):
        key = int(offset), int(bit)
        passed = bool(int(status, 16) & (1 << 32))
        if key[0] == -1 and passed:
            accepted += 1
        elif key in fields and key not in rejected and not passed:
            rejected.add(key)
        else:
            raise ValueError(f"unexpected RTL result for {key}, status={status}")

    n = len(fields)
    footer = f"RTL mutation campaign rejected={n} launched={n} planned={n}"
    if (not fields or rejected != fields.keys() or accepted != 1 or
            footer not in log.splitlines() or "AUTO PASS" not in log.splitlines()):
        raise ValueError(f"incomplete mutation campaign in {transcript}")

    print(f"{transcript.name} matched all {n} manifest bits and accepted the unmodified proof")
    counts = Counter(fields[k] for k in rejected)
    if envelope_only:
        for offset, bit in sorted(k for k in rejected if fields[k] == "envelope"):
            print(f"envelope byte={offset} bit={bit} rejected")
    else:
        for field, count in sorted(counts.items()):
            print(f"{field} rejected={count}")


if __name__ == "__main__":
    report(Path(sys.argv[1]), Path(sys.argv[2]), "--envelope" in sys.argv[3:])
