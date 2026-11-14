#!/usr/bin/env python3
"""Compatibility entry point; the repository root owns the audit policy."""
import runpy
from pathlib import Path

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).resolve().parents[3] / 'scripts/audit_elf_ct.py'), run_name='__main__')
