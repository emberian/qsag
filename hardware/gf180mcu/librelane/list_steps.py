#!/usr/bin/env python3
"""Print the step IDs of the LibreLane `Chip` flow (to run the flow in bounded chunks)."""
from librelane.flows import Flow

print(" ".join(s.id for s in Flow.factory.get("Chip").Steps))
